/*
    httperf wrichlog.c
    Based on Mark Nottingham's patch https://groups.google.com/forum/#!topic/httperf-dev/Wql5eu8cd0U

    Based on httperf's wlog.c
    Copyright (C) 2000  Hewlett-Packard Company
    Contributed by Stephane Eranian <eranian@hpl.hp.com>

    This program is free software; you can redistribute it and/or
    modify it under the terms of the GNU General Public License as
    published by the Free Software Foundation; either version 2 of the
    License, or (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
    General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program; if not, write to the Free Software
    Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA
    02111-1307 USA
*/

/*
 * This load generator can be used to recreate a workload based on a server
 * log file.
 * 
 * 
 * % httperf .... --wrichlog y,my_uri_file
 * 
 */

#include "config.h"

#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <unistd.h>

#include <generic_types.h>

#include <object.h>
#include <timer.h>
#include <httperf.h>
#include <call.h>
#include <conn.h>
#include <core.h>
#include <localevent.h>


#define BUF_SIZE (8 * 1024)
#define MAX_INLINE_CONTENT_SIZE (1024)
#define MAX_LINE (MAX_INLINE_CONTENT_SIZE + 4096)

#ifndef TRUE
#define TRUE  (1)
#endif
#ifndef FALSE
#define FALSE (0)
#endif

/* Methods allowed for a request: */
enum {
    HM_DELETE, HM_GET, HM_HEAD, HM_OPTIONS, HM_POST, HM_PUT, HM_TRACE,
    HM_LEN
};


static const char *call_method_name[] =
{
    "DELETE", "GET", "HEAD", "OPTIONS", "POST", "PUT", "TRACE"
};


/*
 * define a linked list of request objects
 */
typedef struct req REQ;
struct req {
    REQ            *next;
    int             method;
    char           *uri;
    int             uri_len;
    char           *contents;
    int             contents_len;
    char            extra_hdrs[4096];   /* some cookies are really
                         * big */
    int             extra_hdrs_len;
};

static REQ     *cur_req_ptr;

/*
 * Allocates memory for a REQ and assigns values to data members. This is
 * used during configuration file parsing only.
 */
static REQ     *
new_request(char *uristr)
{
    REQ            *retptr;

    retptr = (REQ *) malloc(sizeof(*retptr));
    if (retptr == NULL || uristr == NULL)
        panic("%s: ran out of memory while parsing %s\n",
              prog_name, param.wrichlog.file);

    memset(retptr, 0, sizeof(*retptr));
    retptr->uri = uristr;
    retptr->uri_len = strlen(uristr);
    retptr->method = HM_GET;
    return retptr;
}

static void
free_request_concat(REQ * reqptr)
{
    if (reqptr != NULL) {
        REQ            *nextptr = reqptr->next;
        if (reqptr->uri) {
            free(reqptr->uri);
            reqptr->uri = NULL;
        }
        if (reqptr->contents) {
            free(reqptr->contents);
            reqptr->contents = NULL;
        }
        if (nextptr) {
            reqptr->next = NULL;
            free_request_concat(nextptr);
        } else {
            free(reqptr);
        }
    }
}



static void 
parse_arg(char input[], char arg_contents[], int *bytes_read)
{
    char           *from = strchr(input, '=') + 1;
    char           *to = arg_contents;
    int             single_quoted = FALSE;
    int             double_quoted = FALSE;
    int             escaped = FALSE;
    int             done = FALSE;
    int             ch;
    while ((ch = *from++) != '\0' && !done) {
        if (escaped == TRUE) {
            switch (ch) {
            case 'n':
                *to++ = '\n';
                break;
            case 'r':
                *to++ = '\r';
                break;
            case 't':
                *to++ = '\t';
                break;
            case '\n':
                panic("%s: premature EOF seen in '%s'\n",
                      prog_name, arg_contents);
            default:
                *to++ = ch;
                break;
            }
            escaped = FALSE;
        } else if (ch == '"' && double_quoted) {
            double_quoted = FALSE;
        } else if (ch == '\'' && single_quoted) {
            single_quoted = FALSE;
        } else {
            switch (ch) {
            case '\t':
            case '\n':
            case ' ':
                if (single_quoted == FALSE &&
                    double_quoted == FALSE)
                    done = TRUE;    /* we are done */
                else
                    *to++ = ch;
                break;
            case '\\':  /* backslash */
                escaped = TRUE;
                break;
            case '"':   /* double quote */
                if (single_quoted)
                    *to++ = ch;
                else
                    double_quoted = TRUE;
                break;
            case '\'':  /* single quote */
                if (double_quoted)
                    *to++ = ch;
                else
                    single_quoted = TRUE;
                break;
            default:
                *to++ = ch;
                break;
            }
        }
    }
    *to = '\0';
    from--;         /* back up 'from' to '\0' or white-space */
    *bytes_read = from - input;
}



/*
 * Read in a list of uri Method Content from configuration log file and
 * create in-memory data structures from which to assign uri_s to calls. line
 * = uri [method=<Method> [content-type=<content-type>] content] | # comments
 * content = contents=<content-string>|file=<path_to_file> NOTE that fields
 * in uri line are Single space (SP) separated content-type should not
 * conflict with those defined in "--add-header", at most 4 headers (in
 * total)could be added!!!
 */
static void
parse_config(void)
{
    FILE           *fp, *fd;
    int             lineno, i, reqnum;
    char            line[MAX_LINE];
    char            uri[4096];
    char            method_str[16];
    char            cont_type[128];
    char            cookie[2048];
    char            header[2048];
    char            file_path[512];
    char            this_arg[MAX_LINE];
    char            tmp_contents[MAX_INLINE_CONTENT_SIZE];
    char           *contents;
    char           *tail;
    int             bytes_read;
    int             read_size;
    REQ            *reqptr, *pre_reqptr, *head_reqptr, *tmp_reqptr;
    char           *parsed_so_far;
    int             ch;


    fp = fopen(param.wrichlog.file, "r");
    if (fp == NULL)
        panic("%s: can't open %s\n", prog_name, param.wrichlog.file);

    head_reqptr = pre_reqptr = NULL;
    reqnum = 0;
    for (lineno = 1; fgets(line, sizeof(line), fp); lineno++) {
        if (line[0] == '#')
            continue;   /* skip over comment lines */

        if (sscanf(line, "%s%n", uri, &bytes_read) != 1) {
            continue;   /* empty line */
        }

        /*
         * looks like a request-specifying line, uri would be the
         * first field
         */
        reqptr = new_request(strdup(uri));
        if (!head_reqptr) {
            head_reqptr = pre_reqptr = reqptr;
        } else {
            pre_reqptr->next = reqptr;
            pre_reqptr = reqptr;
        }

        if (param.wrichlog.do_loop)
            reqptr->next = head_reqptr;
        else
            reqptr->next = NULL;
        reqnum++;

        /* parse rest of line to specify additional parameters */
        parsed_so_far = line + bytes_read;
        while (sscanf(parsed_so_far, " %s%n", this_arg, &bytes_read) == 1) {
            if (sscanf(this_arg, "method=%s", method_str) == 1) {
                for (i = 0; i < HM_LEN; i++) {
                    if (!strncmp(method_str, call_method_name[i],
                         strlen(call_method_name[i]))) {
                        reqptr->method = i;
                        break;
                    }
                }
                if (i == HM_LEN)
                    panic("%s: did not recognize method '%s' in %s\n",
                          prog_name, method_str, param.wrichlog.file);
            } else if (sscanf(this_arg, "content-type=%s", cont_type) == 1) {
                if (strlen(reqptr->extra_hdrs) > 0) {
                    strcat(reqptr->extra_hdrs, "Content-Type: ");
                    strcat(reqptr->extra_hdrs, cont_type);
                    strcat(reqptr->extra_hdrs, "\r\n");
                } else {
                    sprintf(reqptr->extra_hdrs, "Content-Type: %s\r\n",
                        cont_type);
                }
                reqptr->extra_hdrs_len = strlen(reqptr->extra_hdrs);
            } else if (sscanf(this_arg, "cookie=%s", cookie) == 1) {
                parse_arg(parsed_so_far, cookie, &bytes_read);
                if (strlen(reqptr->extra_hdrs) > 0) {
                    strcat(reqptr->extra_hdrs, "Cookie: ");
                    strcat(reqptr->extra_hdrs, cookie);
                    strcat(reqptr->extra_hdrs, "\r\n");
                } else {
                    sprintf(reqptr->extra_hdrs, "Cookie: %s\r\n",
                        cookie);
                }
                reqptr->extra_hdrs_len = strlen(reqptr->extra_hdrs);
            } else if (sscanf(this_arg, "header=%s", header) == 1) {
                parse_arg(parsed_so_far, header, &bytes_read);
                if (strlen(reqptr->extra_hdrs) > 0) {
                    strcat(reqptr->extra_hdrs, header);
                    strcat(reqptr->extra_hdrs, "\r\n");
                } else {
                    sprintf(reqptr->extra_hdrs, "%s\r\n",
                        header);
                }
                reqptr->extra_hdrs_len = strlen(reqptr->extra_hdrs);
            } else if (sscanf(this_arg, "file=%s", file_path) == 1) {
                char            buffer[BUF_SIZE];
                struct stat     stat_buf;
                stat(file_path, &stat_buf);
                fd = fopen(file_path, "r");
                if (fd == NULL)
                    panic("%s: can't open content file %s\n", prog_name, file_path);
                contents = (char *) malloc(sizeof(char) * stat_buf.st_size);
                if (!contents)
                    panic("Can not allocate enough memory for %s\n", file_path);
                tail = contents;
                while (1) {
                    read_size = fread(buffer, 1, sizeof(buffer), fd);
                    if (read_size == 0)
                        break;
                    if (read_size < 0) 
                        panic("%s: read error in file %s\n", prog_name, file_path);
                    tail = (char *) memcpy(tail, buffer, read_size) + read_size;
                } 
                fclose(fd);
                reqptr->contents = contents;
                reqptr->contents_len = stat_buf.st_size;
            /*    free(contents);  */
            } else if (sscanf(this_arg, "contents=%s", tmp_contents) == 1) {
                parse_arg(parsed_so_far, tmp_contents, &bytes_read);
                reqptr->contents = strdup(tmp_contents);
                reqptr->contents_len = strlen(tmp_contents);
            } else {
                /* do not recognize this arg */
                panic("%s: did not recognize arg '%s' in $%s in file %s\n",
                      prog_name, this_arg, line, param.wrichlog.file);
            }

            /* generate Content-Length if needed */
            if (reqptr->contents_len > 0) {
                if (strlen(reqptr->extra_hdrs) > 0) {
                    char            tmp_str[64];
                    sprintf(tmp_str, "Content-Length: %d\r\n",
                          reqptr->contents_len);
                    strcat(reqptr->extra_hdrs, tmp_str);
                } else {
                    sprintf(reqptr->extra_hdrs, "Content-Length: %d\r\n",
                          reqptr->contents_len);
                }
                reqptr->extra_hdrs_len = strlen(reqptr->extra_hdrs);
            }

            parsed_so_far += bytes_read;
        }
    }
    fclose(fp);

    cur_req_ptr = head_reqptr;
    if (DBG > 3 || verbose) {
        fprintf(stderr, "%s: %d requests are listed as follows (defined in %s):\n\n",
            prog_name, reqnum, param.wrichlog.file);
        tmp_reqptr = head_reqptr;
        do {
            if (!tmp_reqptr) {
                panic("%s: NULL request met in %s\n", prog_name, param.wrichlog.file);
                continue;
            }
            fprintf(stderr, "%s", tmp_reqptr->uri);

            if (tmp_reqptr->method != HM_GET)
                fprintf(stderr, " method=%s",
                      call_method_name[tmp_reqptr->method]);
            if (tmp_reqptr->extra_hdrs_len > 0)
                fprintf(stderr, " xtra_header=%s", tmp_reqptr->extra_hdrs);
            if (tmp_reqptr->contents != NULL)
                fprintf(stderr, " contents='%s'", tmp_reqptr->contents);
            fprintf(stderr, "\n");

            tmp_reqptr = tmp_reqptr->next;
        } while (tmp_reqptr != NULL && tmp_reqptr != head_reqptr);

        fprintf(stderr, "\ndone printing configure\n");
    }
}

static void
set_request(Event_Type et, Call * c)
{
    assert(et == EV_CALL_NEW && object_is_call(c));

    if (!cur_req_ptr) {
        core_exit();
        call_set_uri(c, "\0", 0);
        return;
    }
    if (cur_req_ptr->method != HM_GET) {
        const char     *method_str;
        method_str = call_method_name[cur_req_ptr->method];
        call_set_method(c, method_str, strlen(method_str));
    }
    call_set_uri(c, cur_req_ptr->uri, cur_req_ptr->uri_len);
    if (cur_req_ptr->extra_hdrs_len > 0) {
        call_append_request_header(c, cur_req_ptr->extra_hdrs,
                       cur_req_ptr->extra_hdrs_len);
    }
    if (cur_req_ptr->contents_len > 0) {
        call_set_contents(c, cur_req_ptr->contents,
                  cur_req_ptr->contents_len);
    }
    if (verbose)
        printf("%s: accessing URI `%s'\n", prog_name, cur_req_ptr->uri);
    cur_req_ptr = cur_req_ptr->next;
}

void
init_wrichlog(void)
{
    Any_Type        arg;
    parse_config();
    arg.l = 0;
    event_register_handler(EV_CALL_NEW, (Event_Handler) set_request, arg);
}

static void
stop_wrichlog(void)
{
    free_request_concat(cur_req_ptr);
}

Load_Generator  uri_wrichlog =
{
    "Generates URIs based on a predetermined list",
    init_wrichlog,
    no_op,
    stop_wrichlog
};
