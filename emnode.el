;;; emnode.el --- a simple emacs async HTTP server -*- lexical-binding: t -*-

;; Copyright (C) 2010, 2011, 2012  Nic Ferrier
;; Copyright (C) 2014  Duong H. Nguyen

;; Author: Nic Ferrier <nferrier@ferrier.me.uk>
;;         Duong H. Nguyen <cmpitg@gmail.com>
;; Maintainer: Duong H. Nguyen <cmpitg@gmail.com>
;; Keywords: lisp, http, hypermedia

;; This file is NOT part of GNU Emacs.

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Source code
;;
;; emnode's code can be found here:
;;   http://github.com/cmpitg/emnode

;;; Commentary:
;;
;; This is an Emacs Lisp version of the popular node.js asynchronous webserver
;; toolkit.
;;
;; You can define HTTP request handlers and start an HTTP server attached to
;; the handler.  Many HTTP servers can be started, each must have it's own TCP
;; port.  Handlers can defer processing with a signal (which allows comet
;; style resource management)
;;

;;; Code:

(require 'fakir)
(require 'mm-encode)
(require 'mailcap)
(require 'url-util)
(require 'kv)
(require 'web)
(require 'json)
(require 'db)
(require 'dired) ; needed for the setup
(require 'ert) ; we provide some assertions and need 'should'
(require 's)
(eval-when-compile (require 'cl))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Const and customization
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst http-referrer 'referer
  "Helper to bypass idiot spelling of the word `referrer'.")

(defconst emnode:+log-none+     0)
(defconst emnode:+log-info+     1)
(defconst emnode:+log-warning+  2)
(defconst emnode:+log-critical+ 3)
(defconst emnode:+log-debug+    4)

(defvar emnode:*log-level* emnode:+log-info+
  "Log level.  Default `emnode:+log-info+'.  Valid values:
`emnode:+log-debug+', `emnode:+log-info+',
`emnode:+log-warning+', `emnode:+log-critical+', `emnode:+log-none+'")

(defgroup emnode nil
  "An extensible asynchronous web server for Emacs."
  :group 'applications)

(defvar emnode-server-socket nil
  "Where we store the server sockets.

This is an alist of proc->server-process:

  (port . process)")

;;;###autoload
(defconst emnode-config-directory
  (expand-file-name (concat user-emacs-directory "emnode/"))
  "The config directory for emnode to store peripheral files.

This is used as a base for other constant directory or file
names (the emnode auth database is a file in this directory, the
emnode webserver has a docroot directory in this directory).

It is based on the `user-emacs-directory' which always seems to
be set, even when emacs is started with -Q.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Error log handling

(defun emnode-trunc (data)
  "Truncate and clean DATA."
  (replace-regexp-in-string
   "[\r\n]" "."
   (substring data 0 (if (> 20 (length data)) (length data) 20))))

(defun emnode-join (&rest parts)
  "Path join the parts together.

EmacsLisp should really provide this by default."
  (let* (savedpart
         (path
          (loop for p in parts
             concat
               (when (> (length p) 0)
                 (setq savedpart p)
                 (file-name-as-directory p)))))
    (if (equal (elt savedpart (- (length savedpart) 1)) ?\/)
        path
        (substring path 0 (- (length path) 1)))))

(defun emnode--dir-setup (dir default default-file-name
                          &optional target-file-name
                          &rest other-files)
  "Install a DIR and DEFAULT-FILE-NAME if it's not setup already.

This is a packaging helper.  It helps an ELPA package install
files from it's package base into the user's Emacs.  If the DIR
is specified under `user-emacs-directory'.

DIR is the directory to install, DEFAULT is the default for that
directory, unless DIR equals DEFAULT nothing is done.

DEFAULT-FILE-NAME is the name of the file that will be installed
in DIR.  It is the expected name of the source file inside the
package.  Unless TARGET-FILE-NAME is specified it is also the
name the installed file will be given.  If the TARGET-FILE-NAME
is specified then that is the the name the file is installed as.

If OTHER-FILES is present it is treated as a list of other
filenames to copy to the DIR."
  (when  (and
          (equal
           dir
           default)
          (not (file-exists-p dir)))
    ;; Do install
    (let ((source-default-file
           (concat
            (file-name-directory
             (or (buffer-file-name)
                 (symbol-file 'emnode--dir-setup))) ; this not very portable
            ;; This should probably tie in with the makefile somehow
            default-file-name)))
      (when (and source-default-file
                 (file-exists-p source-default-file))
        (let ((to (concat
                   dir
                   (or target-file-name default-file-name))))
          (make-directory dir t)
          (message "copying %s emnode wiki default page to %s" dir to)
          (dired-copy-file source-default-file to nil)
          (when other-files
            (flet ((resolve-filename (file)
                     (if (file-name-absolute-p file)
                         file
                         (concat
                          (file-name-directory
                           source-default-file)
                          file))))
              (loop for file in other-files
                 ;; does the file exist?
                 if (and file (file-exists-p (resolve-filename file)))
                 do
                   (dired-copy-file
                    ;; from...
                    (resolve-filename file)
                    ;; to...nd
                    (concat dir (file-name-nondirectory file))
                    nil)))))))))

;;;###autoload
(defmacro emnode-app (dir-var &rest features)
  "A macro that sets up the boring boilerplate for emnode apps.

This sets up lexical binding, captures the module's parent
directory in DIR-VAR, require's `cl' and any other features you
list.  Use it like this:

 (emnode-app my-app-dir esxml mongo-emnode)

Once used you can access the variable `my-app-dir' as the dirname
of your module (which is useful for serving files and such)."
  (declare (indent 2))
  `(progn
     (setq lexical-binding t)
     (defconst ,dir-var (file-name-directory
                         (or (buffer-file-name)
                             load-file-name
                             default-directory)))
     (require 'cl)
     (require 'emnode)
     ,@(loop for f in features
            collect `(require (quote ,f)))))

(defcustom emnode-log-files-directory nil
  "The directory to store any Emnode log files.

If this is not-nil (in which case logs are not saved at all) it
must be the name of a directory Emnode can use for storing logs.
If a directory is specified but it does not exist it is created."
  :group 'emnode
  :type '(choice (const :tag "Off" nil)
          directory))

(defvar emnode-log-buffer-position-written 0
  "The position in the log buffer written.

This is used by `emnode-log-buffer-log' to track what has been written
so far.")

(defvar emnode-log-buffer-max-size 1000
  "Maximum number of lines of log.")

(defvar emnode-log-buffer-datetime-format "%Y%m%d%H%M%S"
  "The date time format used by `emnode-log-buffer-log'.")

(defun emnode-log-buffer-log (text buffer-or-name &optional filename)
  "Log TEXT to the BUFFER-OR-NAME saving the buffer in FILENAME.

BUFFER-OR-NAME is either a buffer or a string naming a buffer.
FILENAME is a filename to save the buffer into.  If the FILENAME
is not specified then we try to use the filename of the
BUFFER-OR-NAME.

If nether a buffer filename nor FILENAME is specified then an
error is generated.

The TEXT is logged with the current date and time formatted with
`emnode-log-buffer-datetime-format'."
  (let ((name (or filename (buffer-file-name (get-buffer buffer-or-name)))))
    (with-current-buffer (get-buffer-create buffer-or-name)
      (unless (assq
               'emnode-log-buffer-position-written
               (buffer-local-variables))
        (make-local-variable 'emnode-log-buffer-position-written)
        (setq emnode-log-buffer-position-written (make-marker))
        (set-marker emnode-log-buffer-position-written (point-min)))
      ;; To test this stuff we could rip these functions out into
      ;; separate pieces?
      (save-excursion
        (goto-char (point-max))
        (insert
         (format
          "%s: %s\n"
          (format-time-string emnode-log-buffer-datetime-format)
          text))
        ;; Save the file if we have a filename
        (when name
          (if (not (file-exists-p (file-name-directory name)))
              (make-directory (file-name-directory name) t))
          ;; could be switched to write-region - probably better
          (append-to-file emnode-log-buffer-position-written (point-max) name)
          (set-marker emnode-log-buffer-position-written (point-max)))
        ;; Truncate the file if it's grown too large
        (goto-char (point-max))
        (forward-line (- emnode-log-buffer-max-size))
        (beginning-of-line)
        (delete-region (point-min) (point))))))

(defcustom emnode-error-log-to-messages t
  "Wether to send emnode logging through the messaging system."
  :group 'emnode
  :type '(boolean))

(defvar emnode-server-error-log "*emnode-server-error*"
  "The buffer where error log messages are sent.")

(defvar emnode--do-error-logging t
  "Allows tests to turn off error logging.")

(defvar emnode--http-send-string-debug nil
  "Whether to do error logging in `emnode-http-send-string'.

That is very high logging, probably a bad idea for anyone but an
emnode developer.")

(defun emnode--get-error-log-buffer ()
  "Returns the buffer for the error-log."
  (get-buffer-create emnode-server-error-log))

(defun emnode-error (msg &rest args)
  "Log MSG with ARGS as an error.

This function is available for handlers to call.  It is also used
by emnode iteslf.

There is only one error log, in the future there may be more."
  (when emnode--do-error-logging
    (let ((filename (emnode--log-filename "emnode-error"))
          (fmtmsg (apply 'format `(,msg ,@args))))
      (emnode-log-buffer-log
       fmtmsg
       (emnode--get-error-log-buffer)
       filename)
      (when emnode-error-log-to-messages
        (message "emnode-error: %s" fmtmsg)))))

(defun emnode--log-filename (logname)
  "Turn LOGNAME into a filename.

`emnode-log-files-directory' is used as the container for log files.

This function mainly exists to make testing easier."
  (when emnode-log-files-directory
    (expand-file-name
     (format "%s/%s"
             emnode-log-files-directory
             logname))))

(defvar emnode-log-access-format-path-width 20)
(defun emnode-log-access-format-func (httpcon)
  "Standard access log format function."
  (format
   (concat
    "%s % 8d %s % "
    (number-to-string emnode-log-access-format-path-width)
    "s")
   (process-get httpcon :emnode-httpresponse-status)
   (or (process-get httpcon :emnode-bytes-written) 0)
   (emnode-http-method httpcon)
   (emnode-http-pathinfo httpcon)))

(defcustom emnode-log-access-default-formatter-function
  'emnode-log-access-format-func
  "The default access log formatter function.

This is used when there is no specific logger function for a
log-name."
  :group 'emnode
  :type 'function)

(defcustom emnode-log-access-alist nil
  "An association list of access log format functions for log names.

An access log format function receives the http connection and
should return a log line to be entered in the log buffer.

These override the default log formatter."
  :group 'emnode
  :type '(alist
          :key-type string
          :value-type function))

(defun emnode-log-access (logname httpcon)
  "Log the HTTP access in buffer LOGNAME.

This function is available for handlers to call.  It is also used
by emnode iteslf."
  (let* ((emnode-log-buffer-datetime-format "%Y-%m-%d-%H:%M:%S")
         (buffer-name (format "*%s-emnode-access*" logname))
         (filename (emnode--log-filename logname))
         (formatter
          (or
           (aget emnode-log-access-alist "emnode")
           emnode-log-access-default-formatter-function))
         (formatted
          (when formatter
            (funcall formatter httpcon))))
    (emnode-log-buffer-log formatted buffer-name filename)))


;; Defer stuff

(progn
  ;; Sets up the emnode defer signal
  (put 'emnode-defer
       'error-conditions
       '(error emnode emnode-defer))
  (put 'emnode-defer
       'error-message
       "Emnode handler processing defered"))

(defvar emnode--deferred '()
  "List of deferred pairs: (socket . handler).")

(defun emnode-defer-now (handler)
  "The function you call to defer processing of the current socket.

Pass in the current HANDLER.

FIXME: We could capture the current handler somehow? I think the
point is that whatever signals emnode-defer should be getting
control back when the deferred is re-processed."
  (signal 'emnode-defer handler))

(defmacro emnode-defer-until (guard &rest body)
  "Test GUARD and defer if it fails and BODY if it doesn't.

`httpcon' is captured in this macro which means the macro can
only be expanded where there is an inscope `httpcon'.

Inside the macro the symbol `emnode-defer-guard-it' is bound to
the value of the GUARD."
  (declare (indent defun))
  (let ((bv (make-symbol "bv"))
        (gv (make-symbol "gv"))
        (fv (make-symbol "fv")))
    `(let* ((,gv (lambda () ,guard))
            (emnode-defer-guard-it (funcall ,gv))
            (,bv (lambda (httpcon) ,@body))
            (,fv ; a y-combinator!
             (lambda (httpcon proc)
               (setq emnode-defer-guard-it (funcall ,gv))
               (if emnode-defer-guard-it
                   (funcall ,bv httpcon)
                   ;; the test failed we should defer again
                   (emnode-defer-now
                    (lambda (http-con)
                      (funcall proc http-con proc)))))))
       (if emnode-defer-guard-it
           (funcall ,bv httpcon)
           ;; The test failed, we should defer.
           (emnode-defer-now
            (lambda (httpcon) ; apply the y-combinator
              (funcall ,fv httpcon ,fv)))))))

(defun emnode--deferred-add (httpcon handler)
  "Add the specified HTTPCON/HANDLER pair to the deferred list."
  (emnode-error "deferred-add: adding a defer %s for %s" handler httpcon)
  (push (cons httpcon handler) emnode--deferred))

(defun emnode--deferred-process-open (httpcon handler)
  "Process the HANDLER with the known open HTTPCON."
  ;; (emnode-error "defer - just before calling the handler %s" handler)
  (funcall handler httpcon))

(defvar emnode-defer-processor-log-level emnode:+log-critical+
  "Log level of the defer processor.")

(defun emnode--deferred-log (level msg &rest args)
  "Special log for emnode-deferreds"
  (when (>= level emnode-defer-processor-log-level)
    (apply
     'emnode-error
     (format "emnode-deferred-processor %s" msg)
     args)))

(defvar emnode-defer-failure-hook nil
  "Hook called when a deferred socket fails.

The hook function is called with the http connection and the
failure state which either the symbol `closed' or the symbol
`failed'.")

(defun emnode--deferred-processor ()
  "Process the deferred queue."
  (let ((run (random 5000)) ; use this to disambiguate runs in the logs
        (new-deferred (list)))
    (emnode--deferred-log emnode-log-info "start")
    (loop for pair in emnode--deferred
       do
         (let ((httpcon (car pair))
               (handler (cdr pair)))
           (case (process-status httpcon)
             ('open
              (emnode--deferred-log emnode-log-info
                                    "open %s %s" httpcon handler)
              (condition-case signal-value
                  (emnode--deferred-process-open httpcon handler)
                ('emnode-defer
                 (push
                  (cons httpcon (cdr signal-value))
                  new-deferred))
                (error
                 (emnode--deferred-log emnode-log-critical
                                       "error %s - %s" httpcon signal-value))))
             ('closed
              (emnode--deferred-log emnode-log-info
                                    "closed %s %s" httpcon handler)
              ;; Call any hook function for defer closes
              (loop for hook-func in emnode-defer-failure-hook
                 do
                   (funcall hook-func httpcon 'closed)))
             ('failed
              (emnode--deferred-log
               emnode-log-info "failed %s %s" httpcon handler)
              ;; Call any hook function for defer failures
              (loop for hook-func in emnode-defer-failure-hook
                 do
                   (funcall hook-func httpcon 'failed)))
             ;; Not sure how to do connect... same as open?
             ;; ... or just put it back?
             ('connect
              (push
               (cons httpcon handler)
               new-deferred)))))
    (emnode--deferred-log emnode-log-info "complete")
    ;; Set the correct queue
    (setq emnode--deferred new-deferred)))

(defun emnode-deferred-queue-process ()
  (interactive)
  (emnode--deferred-processor))

(defvar emnode-defer-on nil
  "Whether to do deferring or not.")

(defvar emnode--defer-timer nil
  "The timer used by the emnode defer processing.

This is initialized by `emnode--init-deferring'.")

(defun emnode--init-deferring ()
  "Initialize emnode defer processing.

Necessary for running comet apps."
  (setq emnode--defer-timer
        (run-at-time "2 sec" 2 'emnode--deferred-processor)))

(defun emnode-deferred-queue (arg)
  "Message the length of the deferred queue."
  (interactive "P")
  (if (not arg)
      (message
       "emnode deferred queue: %d %s"
       (length emnode--deferred)
       emnode--defer-timer)
    (setq emnode--deferred (list))
    (message "emnode deferred queue reset!")))

(defun emnode-deferred-queue-start ()
  "Start the deferred queue, unless it's running."
  (interactive)
  (unless emnode-defer-on
    (setq emnode-defer-on t))
  (unless emnode--defer-timer
    (emnode--init-deferring)))

(defun emnode-deferred-queue-stop ()
  "Stop any running deferred queue processor."
  (interactive)
  (when emnode--defer-timer
    (cancel-timer emnode--defer-timer)
    (setq emnode--defer-timer nil)))

;;; Basic response mangling

(defcustom emnode-default-response-table
  '((201 . "Created")
    (400 . "Bad request")
    (404 . "Not found")
    (500 . "Server error")
    (t . "Ok"))
  "The status code -> default message mappings.

When Emnode sends a default response these are the text used.

Alter this if you want to change the messages that Emnode sends
with the following functions:

 'emnode-send-400'
 'emnode-send-404'
 'emnode-send-500'

The function `emnode-send-status' also uses these."
  :group 'emnode
  :type '(alist :key-type integer
                :value-type string))

(defun emnode--format-response (status &optional msg)
  "Format the STATUS and optionally MESSAGE as an HTML return."
  (format "<h1>%s</h1>%s\r\n"
          (cdr (or (assoc status emnode-default-response-table)
                   (assoc t emnode-default-response-table)))
          (if msg (format "<p>%s</p>" msg) "")))


;; Main control functions

(defun emnode--sentinel (process status)
  "Sentinel function for the main server and for the client sockets."
  (when (>= emnode:*log-level* emnode:+log-info+)
    (emnode-error
     "emnode--sentinel '%s' for process  %s with buffer %s"
     (emnode-trunc status)
     (process-name process)
     (process-buffer process)))
  (cond
    ;; Server status
    ((and
      (assoc (process-contact process :service) emnode-server-socket)
      (equal status "deleted\n"))
     (if (equal
          (process-buffer
           ;; Get the server process
           (cdr (assoc 
                 (process-contact process :service)
                 emnode-server-socket)))
          (process-buffer process))
         (message "found the server process - NOT deleting")
         (message "aha! deleting the connection process")
         (kill-buffer (process-buffer process)))
     (emnode-error "Emnode server stopped"))

    ;; Client socket status
    ((equal status "connection broken by remote peer\n")
     (when (process-buffer process)
       (kill-buffer (process-buffer process))
       (emnode-error "Emnode connection dropped %s" process)))
   
    ((equal status "open\n") ;; this says "open from ..."
     (emnode-error "Emnode opened new connection"))

    ;; Default
    (t
     (when (>= emnode:*log-level* emnode:+log-info+)
       (emnode-error "Emnode status: %s %s" process (s-trim status))))))

(defun emnode--process-send-string (proc data)
  "Emnode adapter for `process-send-string'.

Sends DATA to the HTTP connection PROC (which is an HTTP
connection) using `emnode-http-send-string'.

This is used by `emnode-worker-elisp' to implement a protocol for
sending data through an emnode connection transparently."
  (emnode-http-send-string proc data))

(defun emnode--process-send-eof (proc)
  "Emnode adapter for `process-send-eof'.

Sends EOF to the HTTP connection PROC (which is an HTTP
connection) in a way that chunked encoding is endeed properly.

This is used by `emnode-worker-elisp' to implement a protocol for
sending data through an emnode connection transparently."
  (when (>= emnode:*log-level* emnode:+log-info+)
    (emnode-error "emnode--process-send-eof on %s" proc))
  (emnode-http-send-string proc "")
  ;;(process-send-string proc "\r\n")
  (emnode--http-end proc))

(defun emnode--http-parse (httpcon)
  "Parse the HTTP header for the process.

If the request is not fully complete (if the header has not
arrived yet or we don't have all the content-length yet for
example) this can throw `emnode-parse-http'.  The thing being
waited for is indicated.

Important side effects of this function are to add certain
process properties to the HTTP connection.  These are the result
of succesful parsing."
  ;; FIXME - we don't need to do this - we should check for
  ;; header-parsed and avoid it we we can
  (with-current-buffer (process-buffer httpcon)
    (save-excursion
      (goto-char (point-min))
      (let ((hdrend (re-search-forward "\r\n\r\n" nil 't)))
        (when (not hdrend)
          (throw 'emnode-parse-http 'header))
        ;; FIXME: we don't handle continuation lines of anything like
        ;; that
        (let* ((current-point-header-end (point))
               (lines (split-string
                       (buffer-substring (point-min) hdrend)
                       "\r\n"
                       't))
               (status (car lines)) ;; the first line is the status line
               (header (cdr lines)) ;; the rest of the lines are the header
               (header-alist-strings (mapcar
                                      (lambda (hdrline)
                                        (when (string-match
                                               "\\([A-Za-z0-9_-]+\\):[ ]*\\(.*\\)"
                                               hdrline)
                                          (cons
                                           (match-string 1 hdrline)
                                           (match-string 2 hdrline))))
                                      header))
               (header-alist-syms (mapcar
                                   (lambda (hdr)
                                     (cons (intern (downcase (car hdr)))
                                           (cdr hdr)))
                                   header-alist-strings))
               (data (buffer-substring current-point-header-end (point-max))))
          (process-put httpcon :emnode-header-end hdrend)
          (process-put httpcon :emnode-http-status status)
          (process-put httpcon :emnode-http-header-syms header-alist-syms)
          (process-put httpcon :emnode-http-header header-alist-strings)
          (process-put httpcon :http-data data)))))
  'done)

(defun emnode:http-data (httpcon)
  "Return HTTP data/message/body from `httpcon'.  Note that this
is what the -d/--data directive curl specifies."
  (process-get httpcon :http-data))

(defun emnode--http-make-hdr (method resource &rest headers)
  "Convenience function to make an HTTP header.

METHOD is the method to use.  RESOURCE is the path to use.
HEADERS should be pairs of strings indicating the header values:

 (emnode--http-make-hdr 'get \"/\" '(host . \"localhost\"))

Where symbols are encountered they are turned into strings.
Inside headers they are capitalized.

A header pair with the key `body' can be used to make a content body:

 (emnode--http-make-hdr 'get \"/\" '(body . \"some text\"))
 =>
 GET / HTTP/1.1

 some text

No other transformations are done on the body, no content type
added or content length computed."
  (let (body)
    (flet ((header-name (hdr)
             (if (symbolp (car hdr))
                 (symbol-name (car hdr))
                 (car hdr))))
      (format
       "%s %s HTTP/1.1\r\n%s\r\n%s"
       (upcase (if (symbolp method) (symbol-name method) method))
       resource
       (loop for header in headers
          if (equal (header-name header) "body")
          do (setq body (cdr header))
          else
          concat (format
                  "%s: %s\r\n"
                  (capitalize (header-name header))
                  (cdr header)))
       ;; If we have a body then add that as well
       (or body "")))))


(defun emnode--get-server-prop (process key)
  "Get the value of the KEY from the server attached to PROCESS.

Server properties are bound with `emnode-start' which sets up
`emnode--log-fn' to ensure that all sockets created have a link
back to the server."
  (let* ((server (process-get process :server))
         (value (process-get server key)))
    value))

(defun emnode--make-send-string ()
  "Make a function to send a string to an HTTP connection."
  (lambda (httpcon str)
    "Send STR to the HTTPCON.
Does any necessary encoding."
    (emnode--process-send-string httpcon str)))

(defun emnode--make-send-eof ()
  "Make a function to send EOF to an HTTP connection."
  (lambda (con)
    "Send EOF to the HTTPCON.
Does any necessary encoding."
    (emnode--process-send-eof con)))


(defun emnode--handler-call (handler process)
  "Simple function to wrap calling the HANDLER."
  (when (>= emnode:*log-level* emnode:+log-info+)
    (emnode-error "filter: calling handler on %s" process))
  (funcall handler process)
  (when (>= emnode:*log-level* emnode:+log-info+)
    (emnode-error "filter: handler returned on %s" process)))

(defun emnode--filter (process data)
  "Filtering DATA sent from the client PROCESS..

This does the work of finding and calling the user HTTP
connection handler for the request on PROCESS.

A buffer for the HTTP connection is created, uniquified by the
port number of the connection."
  (let ((buf
         (or
          (process-buffer process)
          ;; Set the process buffer (because the server doesn't
          ;; automatically allocate them)
          ;;
          ;; The name of the buffer has the client port in it
          ;; the space in the name ensures that emacs does not list it
          ;;
          ;; We also use this moment to setup functions required by
          ;; emnode-worker-lisp
          (let* ((port (cadr (process-contact process)))
                 (send-string-func (emnode--make-send-string))
                 (send-eof-func (emnode--make-send-eof)))
            (process-put
             process :send-string-function
             send-string-func)
            ;; ... and this one does closing the connection properly
            ;; with emnode's chunked encoding.
            (process-put
             process :send-eof-function
             send-eof-func)
            ;; Now do the buffer creation
            (set-process-buffer
             process
             (get-buffer-create (format " *emnode-request-%s*" port)))
            (process-buffer process)))))
    (with-current-buffer buf
      (insert data)
      ;; Try and parse...
      (let ((parse-status (catch 'emnode-parse-http
                            (emnode--http-parse process))))
        (case parse-status
          ;; If this fails with one of these specific codes it's
          ;; ok... we'll finish it when the data arrives
          ('(header content)
           (emnode-error "emnode--filter: partial header data received"))
          ;; We were successful so we can call the user handler.
          ('done
           (save-excursion
             (goto-char (process-get process :emnode-header-end))
             (let ((handler
                    (emnode--get-server-prop process :emnode-http-handler)))
               ;; This is where we call the user handler
               ;; TODO: this needs error protection so we can return an error?
               (unwind-protect
                    (condition-case signal-value
                        (emnode--handler-call handler process)
                      ('emnode-defer ; see emnode-defer-now
                       (emnode-error "filter: defer caught on %s" process)
                       ;; Check the timer, this is probably spurious but
                       ;; useful "for now"
                       (unless emnode-defer-on
                         (emnode-error "filter: no defer timer for %s" process))
                       (case (emnode--get-server-prop
                              process :emnode-defer-mode)
                         ((:managed 'managed)
                          (process-put process :emnode-deferred t)
                          (emnode--deferred-add
                           process
                           ;; the cdr of the sig value is the func
                           (cdr signal-value)))
                         ((:immediate 'immediate)
                          (emnode-error "filter: immediate defer on %s" process)
                          (funcall (cdr signal-value) process))))
                      ('t
                       ;; FIXME: we need some sort of check to see if the
                       ;; header has been written
                       (emnode-error
                        "emnode--filter: default handling %S"
                        signal-value)
                       (process-send-string
                        process
                        (emnode--format-response 500))))
                 ;; Handle unwind errors
                 (when
                     (and
                      (not (process-get process :emnode-deferred))
                      (not (process-get process :emnode-http-started))
                      (not (process-get process :emnode-child-process)))
                   (emnode-error "filter: caught an error in the handling")
                   (process-send-string
                    process
                    (emnode--format-response 500))
                   (delete-process process)))))))))))

(defvar emnode--cookie-store nil
  "Cookie store for test servers.

This is a special defvar for dynamic overriding by
`with-emnode-mock-server'.")

(defmacro with-emnode-mock-server (handler &rest body)
  "Execute BODY with a fake server which is bound to HANDLER.

This is useful for doing end to end client testing:

 (ert-deftest emnode-some-page ()
  (with-emnode-mock-server 'emnode-hostpath-default-handler
    (emnode-test-call \"/something/test\")))

The test call with be passed to the
`emnode-hostpath-default-handler' via the normal HTTP parsing
routines."
  (declare
   (indent 1)
   (debug t))
  `(let ((emnode--cookie-store (make-hash-table :test 'equal)))
     (flet ((emnode--get-server-prop (proc key)
              (cond
                ((eq key :emnode-http-handler)
                 ,handler))))
       ,@body)))

(defun emnode--alist-to-query (alist)
  "Turn an alist into a formdata/query string."
  (web--to-query-string alist))

(defun emnode--make-test-call (path method parameters headers)
  "Construct the HTTP request for a test call.

This should probably be merged with the stuff in the `web'
module."
  (let* ((query
          (if (and parameters (equal method "GET"))
              (format
               "?%s"
               (emnode--alist-to-query parameters))
              ""))
         (http-path
          (if (equal query "")
              path
              (format "%s%s" path query)))
         (http-body
          (if (equal method "GET")
              nil
              (let ((param-data (emnode--alist-to-query parameters)))
                (setq headers
                      (append
                       (list
                        (cons "Content-Type"
                              "application/x-www-form-urlencoded")
                        (cons "Content-Length"
                              (format "%d" (length param-data))))
                       headers))
                param-data))))
    (apply
     'emnode--http-make-hdr
     `(,method
       ,http-path
       ,@headers
       (body . ,http-body)))))

(defun emnode--response-header-to-cookie-store (response)
  "Add Set-Cookie headers from RESPONSE to the cookie store."
  (let ((cookie-set (assoc "Set-Cookie" response)))
    (when cookie-set
      (let* ((cookie-value (car (split-string (cdr cookie-set) ";"))))
        (apply
         'puthash
         (append
          (split-string cookie-value "=")
          (list emnode--cookie-store))))))
  emnode--cookie-store)

(defun emnode--cookie-store-to-header-value ()
  "Turn the current cookie store into a header.

The cookies in the header are sorted alphabetically - makes
testing easier."
  (let ((cookie-value
         (mapconcat
          (lambda (cookie)
            (format "%s=%s" (car cookie)
                    (url-hexify-string (cdr cookie))))
          (kvalist-sort
           (kvhash->alist emnode--cookie-store)
           'string-lessp)
          "; ")))
    (unless (equal "" cookie-value)
      cookie-value)))

(defun* emnode-test-call (path
                          &key
                          (method "GET")
                          (parameters '())
                          (headers '()))
  "Fake a call to emnode with the PATH.

In addition you can specify some extra HTTP stuff:

 :method  one of GET, POST, DELETE, etc...
 :parameters POST parameters, will be turned into a POST body
 :headers any specific headers you require, you may override
   test-call headers.

For example:

 (emnode-test-call \"/wiki/test\")

or:

 (emnode-test-call \"/wiki/test\"
                   :method \"POST\"
                   :parameters '((\"a\" . 10)))

For header and parameter names, strings MUST be used currently.

During the test the variable `emnode-webserver-visit-file' is set
to `t' to ensure that Emnode does not pass fake HTTP connections
to external processes."
  (let (result
        (fakir-mock-process-require-specified-buffer t))
    (fakir-mock-process :httpcon ()
      (let ((req (emnode--make-test-call
                  path method parameters
                  (append
                   headers
                   (let ((cookies (emnode--cookie-store-to-header-value)))
                     (when cookies
                       (list (cons "Cookie" cookies)))))))
            (http-connection :httpcon))
        ;; Capture the real eof-func and then override it to do fake ending.
        (let ((eof-func (emnode--make-send-eof))
              (main-send-string (symbol-function 'emnode-http-send-string))
              (send-string-func (emnode--make-send-string))
              (the-end 0)
              (emnode-webserver-visit-file t))
          (flet
              ((emnode-http-send-string (httpcon str)
                 (funcall main-send-string httpcon str))
               (emnode--make-send-string ()
                 (lambda (httpcon str)
                   (funcall send-string-func httpcon str)))
               (emnode--make-send-eof ()
                 (lambda (httpcon)
                   ;; Flet everything in emnode--http-end
                   (flet ((process-send-eof (proc) ;; Signal the end
                            (setq the-end 't))
                          ;; Do nothing - we want the test proc
                          (delete-process (proc))
                          ;; Again, do nothing, we want this buffer
                          (kill-buffer (buffer)
                            ;; Return true, don't really kill the buffer
                            t))
                     ;; Now call the captured eof-func
                     (funcall eof-func httpcon)))))
            ;; FIXME - we should unwind protect this?
            (emnode--filter http-connection req)
            ;; Now we sleep till the-end is true
            (while (not the-end) (sit-for 0.1))
            (when the-end
              (emnode--response-header-to-cookie-store
               (process-get
                http-connection
                :emnode-httpresponse-header))
              ;; Add to the cookie store?
              (setq result
                    (list
                     :result-string
                     (with-current-buffer (fakir-get-output-buffer)
                       (buffer-substring-no-properties (point-min) (point-max)))
                     :buffer
                     (process-buffer http-connection)
                     ;; These properties are set by emnode-http-start
                     :status
                     (process-get
                      http-connection
                      :emnode-httpresponse-status)
                     :header
                     (process-get
                      http-connection
                      :emnode-httpresponse-header))))))))
    ;; Finally return the result
    result))

(defmacro* should-emnode-response (call
                                   &key
                                   status-code
                                   header-name
                                   header-value
                                   header-list
                                   header-list-match
                                   body-match)
  "Assert on the supplied RESPONSE.

CALL should be an `emnode-test-call', something that can make a
response.  Assertions are done by checking the specified values
of the other parameters to this function.

If STATUS-CODE is not nil we assert that the RESPONSE status-code
is equal to the STATUS-CODE.

If HEADER-NAME is present then we assert that the RESPONSE has
the header and that it's value is the same as the HEADER-VALUE.
If HEADER-VALUE is `nil' then we assert that the HEADER-NAME is
NOT present.

If HEADER-LIST is present then we assert that all those headers
are present and `equal' to the value.

If HEADER-LIST-MATCH is present then we assert that all those
headers are present and `equal' to the value.

If BODY-MATCH is present then it is a regex used to match the
whole body of the RESPONSE."
  (let ((status-codev (make-symbol "status-codev"))
        (header-namev (make-symbol "header-namev"))
        (header-valuev (make-symbol "header-valuev"))
        (header-listv (make-symbol "header-listv"))
        (header-list-matchv (make-symbol "header-list-match"))
        (body-matchv (make-symbol "body-matchv"))
        (responsev (make-symbol "responsev")))
    `(let ((,responsev ,call)
           (,status-codev ,status-code)
           (,header-namev ,header-name)
           (,header-valuev ,header-value)
           (,header-listv ,header-list)
           (,header-list-matchv ,header-list-match)
           (,body-matchv ,body-match))
       (when ,status-codev
         (should
          (equal
           ,status-codev
           (plist-get ,responsev :status))))
       (when (or ,header-namev ,header-listv ,header-list-matchv)
         (let ((hdr (plist-get ,responsev :header)))
           (when ,header-namev
             (if ,header-valuev
                 (should
                  (equal
                   ,header-valuev
                   (assoc-default ,header-namev hdr)))
                 ;; Else we want to ensure the header isn't there
                 (should
                  (eq nil (assoc-default ,header-namev hdr)))))
           (when ,header-listv
             (loop for reqd-hdr in ,header-listv
                do (should
                    (equal
                     (assoc-default (car reqd-hdr) hdr)
                     (cdr reqd-hdr)))))
           (when ,header-list-matchv
             (loop for reqd-hdr in ,header-list-matchv
                do (should
                    (>=
                     (string-match
                      (cdr reqd-hdr)
                      (assoc-default (car reqd-hdr) hdr)) 0))))))
       (when ,body-matchv
         (should (string-match ,body-matchv
                               (plist-get ,responsev :result-string)))))))

(defun emnode--log-fn (server con msg)
  "Log function for emnode.

Serves only to connect the server process to the client processes"
  (process-put con :server server))

(defvar emnode-handler-history '()
  "The history of handlers bound to servers.")

(defvar emnode-port-history '()
  "The history of ports that servers are started on.")

(defvar emnode-host-history '()
  "The history of hosts that servers are started on.")

(defun emnode-ports ()
  "List of all ports currently in use by emnode."
  (mapcar 'car emnode-server-socket))

;;;###autoload
(defun emnode-list ()
  (interactive)
  "List the Emnode servers we have running."
  (with-current-buffer (get-buffer-create "*emnode servers*")
    (setq buffer-read-only t)
    (unwind-protect
         (let ((inhibit-read-only t))
           (erase-buffer)
           (loop for server in emnode-server-socket
              do
                (destructuring-bind (port . socket-proc) server
                  (let ((fn (process-get socket-proc :emnode-http-handler)))
                    (princ
                     (format
                      "%s on %s\n%s\n\n"
                      port
                      (process-get socket-proc :emnode-http-handler)
                      (or (documentation fn) "no documentation."))
                   (current-buffer)))))
           (switch-to-buffer (current-buffer))))))

;;;###autoload
(defun* emnode-start (request-handler
                      &key
                      port
                      (host "localhost")
                      (defer-mode :managed))
  "Start a server using REQUEST-HANDLER.

REQUEST-HANDLER will handle requests on PORT on HOST (which is
'localhost' by default).

REQUEST-HANDLER is a function which is called with the request.
The function is called with one argument, which is the
http-connection.

You can use functions such as `emnode-http-start' and
`emnode-http-send-body' to send the http response.

Example:

  (defun nic-server (httpcon)
    (emnode-http-start httpcon 200 '(\"Content-Type\" . \"text/html\"))
    (emnode-http-return httpcon \"<html><b>BIG!</b></html>\"))
  (emnode-start 'nic-server)

Now visit http://127.0.0.1:8000

If PORT is non-nil, then run server on PORT, otherwise default to
8000.

If HOST is non-nil, then run the server on the specified local IP
address, otherwise use localhost.  A few names are predefined:

  \"localhost\" is 127.0.0.1
  \"*\" is 0.0.0.0

Additionally, you may specifiy an IP address, e.g \"1.2.3.4\"

Note that although HOST may be specified, emnode does not
disambiguate on running servers by HOST.  So you cannot start two
emnode servers on the same port on different hosts."
  (interactive
   (let ((handler (completing-read "Handler function: "
                                   obarray 'fboundp t nil nil))
         (port (read-number "Port: " 8000))
         (host (read-string "Host: " "localhost" 'emnode-host-history)))
     (list (intern handler) :port port :host host)))
  (let ((port (or port 8000))
        (host (or host "localhost")))
    (unless (assoc port emnode-server-socket)
      ;; Add a new server socket to the list
      (setq emnode-server-socket
            (cons
             (cons port
                   (let ((buf (get-buffer-create "*emnode-webserver*")))
                     (make-network-process
                      :name "*emnode-webserver-proc*"
                      :buffer buf
                      :server t
                      :nowait 't
                      :host (cond
                             ((equal host "localhost") 'local)
                             ((equal host "*") nil)
                             (t host))
                      :service port
                      :coding '(raw-text-unix . raw-text-unix)
                      :family 'ipv4
                      :filter 'emnode--filter
                      :sentinel 'emnode--sentinel
                      :log 'emnode--log-fn
                      :plist (list
                              :emnode-http-handler request-handler
                              :emnode-defer-mode defer-mode))))
             emnode-server-socket)))))

;; TODO: make this take an argument for the
(defun emnode-stop (port)
  "Stop the emnode server attached to PORT."
  (interactive (let ((prt
                      (string-to-number
                       (completing-read
                        "Port: "
                        (mapcar (lambda (n) (format "%d" n))
                                (emnode-ports))))))
                 (list prt)))
  (let ((server (assoc port emnode-server-socket)))
    (when server
      (message "deleting server process")
      (delete-process (cdr server))
      (setq emnode-server-socket
	    ;; remove-if
	    (let ((test (lambda (elem)
			  (= (car elem) port)))
		  (l emnode-server-socket)
		  result)
	      (while (car l)
		(let ((p (pop l))
		      (r (cdr l)))
		  (if (not (funcall test p))
		      (setq result (cons p result)))))
	      result)))))

(defun emnode-find-free-service ()
  "Return a free (unused) TCP port.

The port is chosen randomly from the ephemeral ports. "
  (let (myserver
        (port 50000)) ; this should be ephemeral base
    (while
        (not
         (processp
          (condition-case sig
              (setq myserver
                    (make-network-process
                     :name "*test-proc*"
                     :server t
                     :nowait 't
                     :host 'local
                     :service port
                     :family 'ipv4))
            (file-error
             (if (equal
                  "Cannot bind server socket address already in use"
                  (mapconcat 'identity (cdr sig) " "))
                 (setq port (+ 50000 (random 5000)))))))))
    (delete-process myserver)
    port))


(defun emnode-list-buffers ()
  "List the current buffers being managed by Emnode."
  (interactive)
  (with-current-buffer (get-buffer-create "*emnode-buffers*")
    (erase-buffer)
    (mapc
     (lambda (b)
       (save-excursion
         (if (string-match " \\*emnode-.*" (buffer-name b))
             (insert (format "%s\n" b)))
       ))
     (sort (buffer-list)
           (lambda (a b)
             (string-lessp (buffer-name b) (buffer-name a))))))
  (display-buffer (get-buffer "*emnode-buffers*")))

(defun emnode-time-encode (time-str)
  "Basic TIME-STR to time encoding."
  (apply 'encode-time (parse-time-string time-str)))


;; HTTP API methods

(defun emnode--http-hdr (httpcon)
  "Return the header cons for the HTTPCON.

The status-line and the header alist."
  (cons
   (process-get httpcon :emnode-http-status)
   (process-get httpcon :emnode-http-header)))

(defun emnode-http-header (httpcon name &optional convert)
  "Get the header specified by NAME from the HTTPCON.

HEADER may be a string or a symbol.  If NAME is a symbol it is
case insensitve.

If optional CONVERT is specified it may specify a conversion,
currently supported conversions are:

 :time - to convert a time value properly"
  (let* ((key (if (symbolp name)
                  (intern (downcase (symbol-name name)))
                name))
         (hdr (process-get
               httpcon
               (if (symbolp key)
                   :emnode-http-header-syms
                 :emnode-http-header)))
         (val (cdr (assoc key hdr))))
    (case convert
      (:time
       (when val
         (emnode-time-encode val)))
      (t
       val))))

(defun* emnode-http-host (httpcon &key split just-host)
  "Return the HTTP `host' name header.

With SPLIT return a list of the hostname and any port part (the
port part might be empty if not specifically specified).  With
JUST-HOST return just the host-name part, dropping any port entirely."
  (let ((host (emnode-http-header httpcon "Host")))
    (cond
      (split
       (string-match "\\([^:]+\\)\\(:\\([0-9]+\\)\\)*" host)
       (list (match-string-no-properties 1 host)
             (match-string-no-properties 3 host)))
      (just-host
       (string-match "\\([^:]+\\)\\(:\\([0-9]+\\)\\)*" host)
       (match-string-no-properties 1 host))
      (t
       host))))

(defun emnode-http-cookies (httpcon)
  "Return the list of cookies attached to this HTTPCON.

The list of cookies is an alist."
  (or
   (process-get httpcon :emnode-http-cookie-list)
   (let* ((cookie-hdr (emnode-http-header httpcon "Cookie"))
          (lst (when cookie-hdr
                 (kvalist-sort
                  (mapcar
                   (lambda (pair)
                     (cons
                      (url-unhex-string (car pair))
                      (url-unhex-string (cdr pair))))
                   (url-parse-args cookie-hdr))
                  'string-lessp))))
     (process-put httpcon :emnode-http-cookie-list lst)
     lst)))

(defun emnode-http-cookie (httpcon name &optional cookie-key)
  "Return the cookie value for HTTPCON specified by NAME.

The cookie is a cons:

  name . value

If COOKIE-KEY is `t' then only the value is returned, else the
cons is returned."
  (let* ((cookie-list (emnode-http-cookies httpcon))
         (cookie (assoc-string name cookie-list)))
    (if cookie-key
        (cdr cookie)
        cookie)))


(defun emnode--http-parse-status (httpcon &optional property)
  "Parse the status line of HTTPCON.

If PROPERTY is non-nil, then return that property."
  (let ((http-line (process-get httpcon :emnode-http-status)))
    (string-match
     "\\(GET\\|POST\\|HEAD\\) \\(.*\\) HTTP/\\(1.[01]\\)"
     http-line)
    (process-put httpcon :emnode-http-method (match-string 1 http-line))
    (process-put httpcon :emnode-http-resource (match-string 2 http-line))
    (process-put httpcon :emnode-http-version (match-string 3 http-line))
    (if property
        (process-get httpcon property))))

(defun emnode--http-parse-resource (httpcon &optional property)
  "Convert the specified resource to a path and a query."
  (save-match-data
    (let ((resource
           (or
            (process-get httpcon :emnode-http-resource)
            (emnode--http-parse-status httpcon :emnode-http-resource))))
      (or
       ;; root pattern
       (string-match "^\\(/\\)\\(\\?.*\\)*$" resource)
       ;; /somepath or /somepath/somepath
       (string-match "^\\(/[^?]+\\)\\(\\?.*\\)*$" resource))
      (let ((path (url-unhex-string (match-string 1 resource))))
        (process-put httpcon :emnode-http-pathinfo path))
      (if (match-string 2 resource)
          (let ((query (match-string 2 resource)))
            (string-match "\\?\\(.+\\)" query)
            (if (match-string 1 query)
                (process-put
                 httpcon
                 :emnode-http-query
                 (match-string 1 query)))))))
  (if property
      (process-get httpcon property)))

(defun emnode-http-pathinfo (httpcon)
  "Get the PATHINFO of the request."
  (or
   (process-get httpcon :emnode-http-pathinfo)
   (emnode--http-parse-resource httpcon :emnode-http-pathinfo)))

(defun emnode-http-query (httpcon)
  "Get the QUERY of the request."
  (or
   (process-get httpcon :emnode-http-query)
   (emnode--http-parse-resource httpcon :emnode-http-query)))

(defun emnode--http-param-part-decode (param-thing)
  "Decode an HTTP URL parameter part.

For example in:

 http://nic.ferrier.me.uk/blog/emnode/?p=10&a+c=20&d=x+y&z=this%20is%09me+and%20this

The following are param parts and the decoding that this function
will do:

 \"p\" ->  \"p\"

 \"10\" -> \"10\"

 \"a+c\" -> \"a c\" - an example of + encoding

 \"d\" -> \"d\"

 \"x+y\" -> \"x y\" - another example of + encoding, in a parameter name

 \"z\" -> \"z\"

 \"this%20is%09me+and%20this\" -> \"this is\tme and this\" -
 percent encoding and plus encoding"
  (url-unhex-string (replace-regexp-in-string "\\+" " " param-thing) 't)
  )

(defun emnode--http-query-to-alist (query)
  "Crap parser for HTTP QUERY data.

Returns an association list."
  (let ((alist (mapcar
                (lambda (nv)
                  (if (string-match "\\([^=]+\\)\\(=\\(.*\\)\\)*" nv)
                      (cons
                       (emnode--http-param-part-decode (match-string 1 nv))
                       (if (match-string 2 nv)
                           (emnode--http-param-part-decode (match-string 3 nv))
                         nil))))
                (split-string query "&"))
               ))
    alist))

(defun emnode--alist-merge (a b &optional operator)
  "Merge two association lists non-destructively.

A is considered the priority (it's elements go in first)."
  (if (not operator)
      (setq operator 'assq))
  (let* ((res '()))
    (let ((lst (append a b)))
      (while lst
        (let ((item (car-safe lst)))
          (setq lst (cdr-safe lst))
          (let* ((key (car item))
                 (aval (funcall operator key a))
                 (bval (funcall operator key b)))
            (if (not (funcall operator key res))
                (setq res (cons
                           (if (and aval bval)
                               ;; the item is in both lists
                               (cons (car item)
                                     (list (cdr aval) (cdr bval)))
                             item)
                           res))))))
        res)))

(defun emnode--http-post-to-alist (httpcon)
  "Parse the POST body."
  ;; FIXME: this is ONLY a content length header parser it should also
  ;; cope with transfer encodings.
  (let ((postdata
         (with-current-buffer (process-buffer httpcon)
           ;; (buffer-substring (point-min) (point-max)) ;debug
           (buffer-substring
            ;; we might have to add 2 to this because of trailing \r\n
            (process-get httpcon :emnode-header-end)
            (point-max)))))
    (emnode--http-query-to-alist postdata)))

(defun emnode-http-params (httpcon &rest names)
  "Get an alist of the parameters in the request.

If the method is a GET then the parameters are from the url. If
the method is a POST then the parameters may come from either the
url or the POST body or both:

 POST /path?a=b&x=y
 a=c

would result in:

 '(('a' 'b' 'c')('x' . 'y'))

If NAMES are specified it is a filter list of symbols or strings
which will be returned."
  (loop for pair in
       (or
        (process-get httpcon :emnode-http-params)
        (let ((query (emnode-http-query httpcon)))
          (let ((alist (if query
                           (emnode--http-query-to-alist query)
                           '())))
            (if (equal "POST" (emnode-http-method httpcon))
                ;; If we're a POST we have to merge the params
                (progn
                  (setq alist
                        (emnode--alist-merge
                         alist
                         (emnode--http-post-to-alist httpcon)
                         'assoc))
                  (process-put httpcon :emnode-http-params alist)
                  alist)
                ;; Else just return the query params
                (process-put httpcon :emnode-http-params alist)
                alist))))
     if (or (not names)
            (memq (intern (car pair)) names)
            (member (car pair) names))
     collect pair))

(defun emnode-http-param (httpcon name)
  "Get the named parameter from the request."
  (let* ((params (emnode-http-params httpcon))
         (param-pair
          (assoc
           (if (symbolp name) (symbol-name name) name)
           params)))
    ;; Should we signal when we don't have a param?
    (when param-pair
      (cdr param-pair))))

(defun emnode-http-method (httpcon)
  "Get the PATHINFO of the request."
  (or
   (process-get httpcon :emnode-http-method)
   (emnode--http-parse-status httpcon :emnode-http-method)))

(defun emnode-http-version (httpcon)
  "Get the PATHINFO of the request."
  (or
   (process-get httpcon :emnode-http-version)
   (emnode--http-parse-status httpcon :emnode-http-version)))

(defun emnode-http-send-string (httpcon str)
  "Send STR to HTTPCON, doing chunked encoding."
  (if emnode--http-send-string-debug
      (when (>= emnode:*log-level* emnode:+log-info+)
        (emnode-error
         "emnode-http-send-string %s [[%s]]"
         httpcon (emnode-trunc str))))
  (let ((len (string-bytes str)))
    (process-put httpcon :emnode-bytes-written
                 (+ len (or (process-get httpcon :emnode-bytes-written) 0)))
    ;; FIXME Errors can happen here, because the socket goes away.. it
    ;; would be nice to trap them and report and then re-raise them.
    (process-send-string httpcon (format "%x\r\n%s\r\n" len (or str "")))))

(defvar emnode-http-codes-alist
  (loop for p in '((200 . "Ok")
                   (302 . "Redirect")
                   (400 . "Bad Request")
                   (401 . "Authenticate")
                   (404 . "Not Found")
                   (500 . "Server Error"))
        collect
        p
        collect
        (cons (number-to-string (car p))
              (cdr p)))
  "HTTP codes with string keys and integer keys.")


(defun* emnode-http-cookie-make (name data &key expiry path)
  "Make a set-cookie header pair from NAME and DATA.

DATA should be a string to be used as the value of the cookie.

Other key values are standard cookie attributes.

Use this with `emnode-http-start' to make cookie headers:

 (emnode-http-start
    httpcon 200
    '(content-type . \"text/html\")
    (emnode-http-cookie-make \"pi\" 3.14579)
    (emnode-http-cookie-make \"e\" 1.59
       :expiry \"Mon, Feb 27 2012 22:10:21 GMT;\")

This will send two Set-Cookie headers setting the cookies 'pi'
and 'e'.

The return value is a cons pair."
  (cons
   "Set-Cookie"
   (format "%s=%s;%s"
           name
           data
           (if (not (or expiry
                        path))
               ""
               (loop for p in `((expires . ,expiry)
                                (path . ,path))
                  if (cdr p)
                  concat
                    (format
                     " %s=%s;"
                     (capitalize (symbol-name (car p)))
                     (cdr p)))))))

(defun emnode-http-header-set (httpcon header &optional value)
  "Sets the HEADER for later processing.

HEADER may be a pair of `name' and `value' or it may just be a
String, or a Symbol in which case the VALUE must be specified.

If HEADER is a pair and VALUE is also specified then VALUE is
ignored.

When the HTTP response is started any set headers will be merged
with any requested headers and sent.

If the response has been started it is an error to try to set a
header.  This function will log the error and return `nil'.

See `emnode-http-start'."
  (if (process-get httpcon :emnode-http-started)
      (emnode-error "can't set header, HTTP already started on %s" httpcon)
      (let ((headers (process-get httpcon :emnode-headers-to-set)))
        (process-put
         httpcon
         :emnode-headers-to-set
         (append headers
                 (list (if (consp header)
                           header
                           (cons header value))))))))

(defun emnode--http-result-header (hdr-alist)
  "Turn the HDR-ALIST into a result header string.

The HDR-ALIST is an alist of symbol or string keys which are
header names, against values which should be strings."
  (let ((hdr-pairs
         (append
          (list (cons 'transfer-encoding "chunked"))
          hdr-alist)))
    (loop for p in hdr-pairs
       concat
         (format
          "%s: %s\r\n"
          (let ((hname (car p)))
            (capitalize
             (cond
               ((symbolp hname)
                (symbol-name hname))
               ((stringp hname)
                hname)
               (t
                (error "unsupported header type")))))
          (cdr p)))))

(defun emnode-http-start (httpcon status &rest header)
  "Start the http response on the specified http connection.

HTTPCON is the HTTP connection being handled.

STATUS is the HTTP status, eg: 200 or 404; integers or strings
are acceptable types.

HEADER is a sequence of (`header-name' . `value') pairs.

For example:

 (emnode-http-start httpcon \"200\" '(\"Content-type\" . \"text/html\"))

The status and the header are also stored on the process as meta
data.  This is done mainly for testing infrastructure."
  (if (process-get httpcon :emnode-http-started)
      (emnode-error "Http already started on %s" httpcon)
      ;; Send the header
      (when (>= emnode:*log-level* emnode:+log-info+)
        (emnode-error "starting HTTP response on %s" httpcon))
      (let ((header-alist
             (append (process-get httpcon :emnode-headers-to-set) header))
            (status-code (if (stringp status)
                             (string-to-number status)
                             status)))
        ;; Store the meta data about the response.
        (process-put httpcon :emnode-httpresponse-status status-code)
        (process-put httpcon :emnode-httpresponse-header header-alist)
        (process-send-string
         httpcon
         (format
          "HTTP/1.1 %d %s\r\n%s\r\n"
          status-code
          ;; The status text
          (assoc-default status-code emnode-http-codes-alist)
          ;; The header
          (or
           (emnode--http-result-header header-alist)
           "\r\n")))
        (process-put httpcon :emnode-http-started 't))))

(defun emnode--http-end (httpcon)
  "We need a special end function to do the emacs clear up.

This makes access log file calls if the socket has a property
`:emnode-access-log-name'.  The property is taken to be the name
of a buffer."
  (when (>= emnode:*log-level* emnode:+log-info+)
    (emnode-error "emnode--http-end ending socket %s" httpcon))
  (let ((access-log-name (process-get httpcon :emnode-access-log-name)))
    (when access-log-name
      (condition-case err
          (emnode-log-access access-log-name httpcon)
        (error
         (when (>= emnode:*log-level* emnode:+log-warning+)
           (message
            (concat
             "emnode--http-end: an error occurred "
             "processing the access log")))))))
  (condition-case nil
      (process-send-eof httpcon)
    (error (message "emnode--http-endL could not send EOF")))
  (delete-process httpcon)
  (kill-buffer (process-buffer httpcon)))

(defun emnode-http-return (httpcon &optional data)
  "End the response on HTTPCON optionally sending DATA first.

HTTPCON is the http connection which must have had the headers
sent with `emnode-http-start'

DATA must be a string, it's just passed to `emnode-http-send'."
  (if (not (process-get httpcon :emnode-http-started))
      (emnode-error "Http not started")
    (progn
      (if data
          (emnode-http-send-string httpcon data))
      (let ((eof-func (process-get httpcon :send-eof-function)))
        (if (functionp eof-func)
            (funcall eof-func httpcon)
            ;; Need to close the chunked encoding here
            (emnode-http-send-string httpcon ""))))))

(defun emnode-send-html (httpcon html)
  "Simple send for HTML."
  (emnode-http-start httpcon 200 '("Content-Type" . "text/html"))
  (emnode-http-return httpcon html))

(defun emnode-json-fix (data)
  "Fix JSON "
  (let ((json-to-send
         (flet
             ((json-alist-p
                  (list)
                "Proper check for ALIST."
                (while (consp list)
                  (setq list
                        (if (and
                             (consp (car list))
                             (not (consp (caar list)))
                             (not (vectorp (caar list))))
                            (cdr list)
                            'not-alist)))
                (null list)))
           (json-encode data)))) json-to-send))

(defun* emnode-send-json (httpcon data &key content-type jsonp)
  "Send a 200 OK to the HTTPCON along with DATA as JSON.

If CONTENT-TYPE is specified then it is used as the HTTP Content
Type of the response.

If JSONP is specified the content is sent as a JSON-P response.
If the variable specifies a name for the JSON-P callback function
that that is used.  Alternately, if the JSONP parameter does not
specify a name, the parameter `callback' is looked up on the
HTTPCON and the value of that used.  If neither the JSONP
parameter, not the HTTP parameter `callback' is present that the
name \"callback\" is used."
  (let ((json-to-send (emnode-json-fix data)))
    (emnode-http-start
     httpcon 200
     `("Content-type" . ,(or content-type "application/json")))
    (emnode-http-return
     httpcon
     (if jsonp
         (format
          "%s(%s);"
          (or (when (stringp jsonp)
                jsonp)
              (emnode-http-param httpcon "callback")
              "callback")
          json-to-send)
         json-to-send))))

(defun emnode-send-status (httpcon status &optional msg)
  "A generic handler to send STATUS to HTTPCON.

Sends an HTTP response with STATUS to the HTTPCON.  An HTML body
is sent by looking up the STATUS in the `emnode-default-response'
table.

Optionally include MSG."
  (emnode-http-start httpcon status '("Content-type" . "text/html"))
  (emnode-http-return httpcon
                      (emnode--format-response status msg)))

(defun emnode-send-404 (httpcon &optional msg)
  "Sends a Not Found error to the HTTPCON.

Optionally include MSG."
  (emnode-send-status httpcon 404 msg))

(defun emnode-send-400 (httpcon &optional msg)
  "Sends a Bad Request error to the HTTPCON.

Optionally include MSG."
  (emnode-send-status httpcon 400 msg))

(defun emnode-send-500 (httpcon &optional msg)
  "Sends a Server Error to the HTTPCON.

Optionally include MSG."
  (emnode-send-status httpcon 500 msg))

(defun emnode-send-redirect (httpcon location &optional type)
  "Sends a redirect to LOCATION.

If TYPE is non-nil, use it as a status code.  Defaults to 302 -
permanent redirect."
  (let ((status-code (or type 302)))
    (emnode-http-start httpcon status-code `("Location" . ,location))
    (emnode-http-return
     httpcon
     (format "<h1>redirecting you to %s</h1>\r\n" location))))

(defun emnode-normalize-path (httpcon handler)
  "A decorator for HANDLER that normalizes paths to have a trailing slash.

This checks the HTTPCON path for a trailing slash and sends a 302
to the slash trailed url if there is none.

Otherwise it calls HANDLER."
  (let ((ends-in-slash-or-extension-regex ".*\\(/\\|.*\\.[^/]*\\)$")
        (path (emnode-http-pathinfo httpcon)))
    (if (not (save-match-data
               (string-match ends-in-slash-or-extension-regex
                             path)))
        (emnode-send-redirect
         httpcon
         (format "%s/" path))
      (funcall handler httpcon))))

(defun emnode--mapper-find-match-func (match-path match-pair)
  "Funtion to test MATCH-PATH against MATCH-PAIR."
  (let ((m (string-match (car match-pair) match-path)))
    (and m
          (numberp m)
         (>= m 0)
         match-pair)))

(defun emnode--mapper-find-mapping (match-path mapping-table)
  "Return the mapping that matches MATCH-PATH in MAPPING-TABLE."
  (loop for mapping in mapping-table
     if (emnode--mapper-find-match-func match-path mapping)
     return mapping))

(defun emnode--mapper-find (httpcon path mapping-table)
  "Try and find the PATH inside the MAPPING-TABLE.

This function exposes it's `match-data' on the 'path' variable so
that you can access that in your handler with something like:

 (match-string 1 (emnode-http-pathinfo httpcon))

Returns the handler function that mapped, or `nil'.

This function also establishes the `:http-args'
property, adding it to the HTTPCON so it can be accessed from
inside your handler with `emnode:http-get-arg'."
  ;; First find the mapping in the mapping table
  (let ((m (emnode--mapper-find-mapping path mapping-table)))
    ;; Now work out if we found one and what it was mapped to
    (when (and m
               (or (functionp (cdr m))
                   (functionp (and (symbolp (cdr m))
                                   (symbol-value (cdr m))))))
      ;; Make the match parts accessible
      (process-put
       httpcon
       :http-args
       (when (string-match (car m) path)
         (loop for i from 0 to (- (/ (length (match-data path)) 2) 1)
               collect (match-string i path))))
      ;; Check if it's a function or a variable pointing to a
      ;; function
      (cond
       ((functionp (cdr m))
        (cdr m))
       ((functionp (symbol-value (cdr m)))
        (symbol-value (cdr m)))))))

(defun emnode:http-get-arg (httpcon &optional part)
  "Return the match on the HTTPCON that resulted in the current handler.

With PART it returns a specific part of the match , by default
PART is 0.

This results only from a call via `emnode-dispatcher'.

It returns the string which matched your url-mapping, with the
match-data attached. So given the mapping:

 (\"/static/\\(.*\\)\" . my-handler)

and the request:

 /static/somedir/somefile.jpg

The following is true inside the handler:

 (equal \"/somedir/somefile.jpg\"
        (match-string 1 (emnode:http-get-arg httpcon)))

The function `emnode-test-path' uses this facility to work out a
target path."
  (elt
   (process-get httpcon :http-args)
   (if part part 0)))

(defun emnode--strip-leading-slash (str)
  "Strip any leading slash from STR.

If there is no leading slash then just return STR."
  (if (string-match "^/\\(.*\\)" str)
      (match-string 1 str)
      str))

(defun emnode-get-targetfile (httpcon docroot)
  "Get the targetted file from the HTTPCON.

Attempts to resolve the matched path of the HTTPCON against the
DOCROOT.  If that doesn't work then it attempts to use just the
pathinfo of the request.

The resulting file is NOT checked for existance or safety."
  (let* ((pathinfo (emnode-http-pathinfo httpcon))
         (path (emnode:http-get-arg httpcon 1))
         (targetfile
          (emnode-join
           (expand-file-name docroot)
           (emnode--strip-leading-slash
            (or path pathinfo)))))
    targetfile))


;; We need to declare this before the dispatcher stuff, which uses it.
(defvar emnode--defined-authentication-schemes
  (make-hash-table :test 'equal)
  "The hash of defined authentication schemes.")

(defvar emnode--do-access-logging-on-dispatch t
  "Needed to suppress logging in testing.")

(defun emnode--auth-entry->dispatch-table (auth-scheme &optional hostpath)
  "Make a dispatch table from the AUTH-SCHEME.

If HOSTPATH is specified then the resulting match spec is of the
`hostpath' type for use with `emnode-hostpath-dispatcher'."
  (let* ((auth-scheme (gethash
                       auth-scheme
                       emnode--defined-authentication-schemes))
         (redirect (plist-get auth-scheme :redirect))
         (login-handler (plist-get auth-scheme :login-handler)))
    (when redirect
      (list
       (cons
        (concat (if hostpath "^.*/" "^") redirect "$")
        login-handler)))))

(defun* emnode--dispatch-proc (httpcon
                              path
                              url-mapping-table
                              &key
                              (function-404 'emnode-send-404)
                              (log-name "emnode")
                              extra-table)
  "Dispatch to the matched handler for the PATH on the HTTPCON.
The handler for PATH is matched in the URL-MAPPING-TABLE via
`emnode--mapper-find'.

If no handler is found then a 404 is attempted via FUNCTION-404,
it it's found to be a function, or as a last resort
`emnode-send-404'.

The function also supports the searching of the map provided by
an EXTRA-TABLE.  This is useful for authentication and other
wrappers.  If it is specified it is searched first."
  (let ((handler-func
         (or
          ;; Either a match from extra-table ...
          (and extra-table
               (emnode--mapper-find
                httpcon path extra-table))
          ;; ... or from the standard url-mapping-table
          (emnode--mapper-find
           httpcon path url-mapping-table))))
    (when emnode--do-access-logging-on-dispatch
      (process-put httpcon :emnode-access-log-name log-name))
    (cond
     ;; If we have a handler, use it.
     ((functionp handler-func)
      (funcall handler-func httpcon))
     (t
      (funcall function-404 httpcon)))))

(defun* emnode-dispatcher (httpcon
                           url-mapping-table
                           &key
                           (function-404 'emnode-send-404)
                           auth-scheme)
  "Dispatch HTTPCON to the function mapped in URL-MAPPING-TABLE.

URL-MAPPING-TABLE is an alist of:

 (url-regex . function-to-dispatch)

To map the root url you should use:

  \"^/$\"

To ensure paths end in /, `emnode-dispatcher' uses
`emnode-normalize-path'.  To map another url you should use:

  \"^/path/$\" or \"^/path/sub-path/$\"

An example server setup:

  (defun my-server (httpcon)
    (emnode-dispatcher
     httpcon
     '((\"^/$\" . root-view)
       (\"^/1/$\" . view-1))))

If FUNCTION-404 is specified it is called when no regexp is
matched, otherwise `emnode-send-404' is used.

AUTH-SCHEME is an optional authentication scheme, defined with
`emnode-defauth', which specifies a redirect mapping for
authentications."
  (emnode-normalize-path
   httpcon
   (lambda (httpcon)
     ;; Get pathinfo again because we may have redirected.
     (let ((pathinfo (emnode-http-pathinfo httpcon))
           (extra-table
            (emnode--auth-entry->dispatch-table auth-scheme)))
       (emnode--dispatch-proc
        httpcon
        pathinfo
        url-mapping-table
        :function-404 function-404
        :extra-table extra-table)))))

(defun emnode--hostpath (host path)
  "Turn the host and path into a hostpath."
  (format
   "%s/%s"
   (let ((host-name (or host "")))
     ;; Separate the hostname from any port in the host header
     (save-match-data
       (if (string-match "\\([^:]+\\)\\(:[0-9]+.*\\)*" host-name)
           (match-string 1 host-name)
           "")))
   path))

(defun* emnode-hostpath-dispatcher (httpcon
                                   hostpath-mapping-table
                                   &key
                                   (function-404 'emnode-send-404)
                                   (log-name "emnode")
                                   auth-scheme)
  "Dispatch HTTPCON to a handler based on the HOSTPATH-MAPPING-TABLE.

HOSTPATH-MAPPING-TABLE has regexs of the host and the path double
slash separated, thus:

 (\"^localhost//pastebin.*\" . pastebin-handler)

FUNCTION-404 should be a 404 handling function, by default it's
`emnode-send-404'.

LOG-NAME is an optional log-name.

AUTH-SCHEME is an optional authentication scheme, defined with
`emnode-defauth', which specifies a redirect mapping for
authentications."
  (let ((hostpath (emnode--hostpath
                   (emnode-http-header httpcon "Host")
                   (emnode-http-pathinfo httpcon)))
        (extra-table
         ;; Make sure it's a hostpath type
         (emnode--auth-entry->dispatch-table auth-scheme t)))
    (emnode--dispatch-proc
     httpcon
     hostpath
     hostpath-mapping-table
     :function-404 function-404
     :log-name log-name
     :extra-table extra-table)))

;;;###autoload
(defcustom emnode-hostpath-default-table
  '(("[^/]+//wiki/\\(.*\\)" . emnode-wikiserver)
    ("[^/]+//\\(.*\\)" . emnode-webserver))
  "Defines mappings for `emnode-hostpath-default-handler'.

This is the default mapping table for Emnode, out of the box. If
you customize this then emnode will serve these hostpath mappings
by just loading Emnode.

By default the table maps everything to
`emnode-webserver'. Unless you're happy with the default you
should probably get rid of the everything path because it will
interfere with any other mappings you add."
  :group 'emnode
  :type '(alist :key-type string
                :value-type symbol))

(defun emnode-hostpath-default-handler (httpcon)
  "A default hostpath handler.

This uses the `emnode-hostpath-default-table' for the match
table.  It calls `emnode-hostpath-dispatcher' with
`emnode-hostpath-default-table'."
  (emnode-hostpath-dispatcher httpcon emnode-hostpath-default-table))


;; Async handling stuff

(defmacro with-stdout-to-emnode (httpcon &rest body)
  "Execute BODY so that any output gets sent to HTTPCON."
  (declare
   (debug (sexp &rest form))
   (indent defun))
  (let ((hv (make-symbol "httpconvar"))
        (val (make-symbol "value")))
    `(with-temp-buffer
       (let ((,hv ,httpcon)
             (standard-output (current-buffer)))
         (let ((,val (progn ,@body)))
           ;; FIXME - Need a loop here
           (emnode-http-send-string
            ,hv
            (buffer-substring (point-min) (point-max)))
           (emnode-http-return ,hv))))))


;; Emnode child process functions

(defcustom emnode-log-worker-elisp nil
  "If true then worker Elisp (Elisp run in a child-Emacs process) is logged.

The buffer '* emnode-worker-elisp *' is used for the log."
  :group 'emnode
  :type '(boolean))

(defcustom emnode-log-worker-responses nil
  "If true then worker Elisp logs responses in a buffer.

The buffer '* emnode-worker-response *' is used for the log."
  :group 'emnode
  :type '(boolean))

(defun emnode--worker-filter-helper (process
                                     data
                                     child-lisp
                                     out-stream)
  "A helper function for `emnode-worker-elisp'.

Sends DATA being sent from PROCESS to OUT-STREAM.

CHILD-LISP is sent in response to Emacs' query for the Lisp on stdin."
  (if emnode-log-worker-responses
      (with-current-buffer
          (get-buffer-create "* emnode-worker-response *")
        (goto-char (point-max))
        (insert data)))

  ;; Spit out a bit of the data (truncated)
  (emnode-error
   "emnode--worker-filter-helper data %s... %s"
   (emnode-trunc data)
   out-stream)

  ;; We get this as a signal to read a lisp expression
  (if (equal data "Lisp expression: ")
      (process-send-string process child-lisp)
    (cond
     ((bufferp out-stream)
      (with-current-buffer out-stream
        (insert data)))
     ((functionp out-stream)
      (funcall out-stream process data))
     ((processp out-stream)
      (if (not (equal "closed" (process-status process)))
          (funcall
           ;; Does the output-stream have a specific function?
           (or (process-get out-stream :send-string-function)
               'process-send-string)
           ;; The data to sent to the output-stream process
           out-stream data))))))

(defun emnode--worker-lisp-helper (child-lisp)
  "Called with CHILD-LISP it returns a version of CHILD-LISP.

By default this function does nothing except return it's argument.

The function exists so that other functions CAN flet it and thus
override the Lisp being passed to the child Emacs."
  child-lisp)

(defmacro emnode-worker-elisp (output-stream bindings &rest body)
  "Evaluate the BODY in a child Emacs connected to OUTPUT-STREAM.

The BINDINGS are let-form variable assignments which are
serialized for the child Emacs.  Unless a variable from the
parent is explicitly stated here it will NOT be accessible in the
child Emacs.

The child Emacs has a `load-path' exactly as the `load-path' of
the parent Emacs at execution.

The created child Emacs process is returned.  It's possible to
kill the child Emacs process or do other things to it directly.
This could be very dangerous however, you should know what you
are doing before attempting it.

The OUTPUT-STREAM could be a buffer, a function or another
process.

If the OUTPUT-STREAM is another process it may have a process
property `:send-string-function' evaluating to a function to send
data to that process.  The function should take the same
arguments as the standard Emacs Lisp `process-send-string'.

Furthermore, if the OUTPUT-STREAM is another process, when the
child Emacs finishes an EOF is sent to that process.  If the
OUTPUT-STREAM process has a process property `:send-eof-function'
then that is used to send the EOF.  The function should take the
same arguments as the standard Emacs Lisp `process-send-eof'.

An example:

 (emnode-worker-elisp http-connection
                      ((path (path-function)))
   (require 'creole)
   (creole-wiki path))

Presuming http-connection is a process (in the manner of Emnode,
for example) this will cause a child Emacs to be created, within
which `path' (which is serialized from the value of the parent
Emacs' `path-function') will be loaded and converted from
WikiCreole to HTML and then sent to the standard output stream.
The child's standard output stream is connected directly to the
`http-connection'.  In this case, presumably the
`http-connection' would have functions attached to the properties
`:send-string-function' and `:send-eof-function' to do HTTP
chunk encoding and to end the HTTP connection correctly."
  (declare
   (indent 2)
   (debug
    (sexp
     (&rest
      &or symbolp (gate symbolp &optional form))
     &rest form)))
  (let ((loadpathvar (make-symbol "load-path-form"))
        (bindingsvar (make-symbol "bindings"))
        (childlispvar (make-symbol "child-lisp"))
        (childlispfile (make-symbol "child-lisp-file"))
        (filtervar (make-symbol "filter-function"))
        (cmdvar (make-symbol "command"))
        (procvar (make-symbol "process"))
        (namevar (make-symbol "process-name"))
        (bufvar (make-symbol "buffer"))
        (outvar (make-symbol "output-stream")))
    `(let* ((,outvar ,output-stream)
            (,childlispvar  ; the lisp to run
             (concat
              ;; There is a very strange thing with sending lisp to
              ;; (read) over a piped stream... (read) can't cope with
              ;; multiple lines; so we encode newline here.
              (replace-regexp-in-string
               "\n"
               "\\\\n"
               (format "(progn (setq load-path (quote %S)) (let %S %S))"
                       load-path
                       (list
                        ,@(loop
                           for f in bindings collect
                           (list 'list
                                 `(quote ,(car f))
                                 `(format "%s" ,(cadr f)))))
                       '(progn ,@(emnode--worker-lisp-helper body))))
              "\n"))
            (,childlispfile
             (let ((,childlispfile (make-temp-file "emnode")))
               (with-temp-file ,childlispfile
                 (insert ,childlispvar))
               ,childlispfile))
            (,cmdvar
             (concat "emacs -q -batch "
                     "--script " ,childlispfile
                     ));;" 2> /dev/null"))
            (,namevar (concat
                       (number-to-string (random))
                       (number-to-string (float-time))))
            ;; We have to make a buffer unless the output-stream is a buffer
            (,bufvar (cond
                      ((bufferp ,outvar) ,outvar)
                      (t
                       (get-buffer-create (format "* %s *" ,namevar)))))
            (,procvar (start-process-shell-command ,namevar ,bufvar ,cmdvar)))
       ;; Log the lisp
       (if emnode-log-worker-elisp
           (with-current-buffer (get-buffer-create "* emnode-worker-elisp *")
             (insert ,childlispvar)))
       ;; Setup a filter funcion on the child lisp to map output back
       ;; to whatever the output is
       (set-process-filter
        ,procvar
        (lambda (process data)
          (emnode--worker-filter-helper
           process
           data
           ,childlispvar
           ,outvar)))
       ;; Now setup the sentinel
       (set-process-sentinel
        ,procvar
        (lambda (process status)
          ;; Choose or fake a send-eof func
          (emnode-error "emnode-worker-elisp sentinel for %s" ,namevar)
          (let ((send-eof-function
                 (or (and (processp ,outvar)
                          (or (process-get ,outvar :send-eof-function)
                              'process-send-eof))
                     (lambda (con)
                       (emnode-error
                        "emnode-worker-elisp fake eof func %s"
                        ,namevar)))))
            (cond
             ;; Normal end
             ((equal status "finished\n")
              (emnode-error
               "emnode-worker-elisp %s completed %s"
               ,namevar
               ,outvar)
              (funcall send-eof-function ,outvar))
             ;; Error end
             ((string-match "exited abnormally with code \\([0-9]+\\)\n" status)
              (emnode-error
               "emnode-worker-elisp %s completed with an error: %s"
               ,namevar
               status)
              (funcall send-eof-function ,outvar)
              (delete-process process)
              (unless (bufferp ,outvar)
                (kill-buffer (process-buffer process))))
             ;; Any other signal status is ignored
             (t)))))
       ,procvar)))

(defun emnode-wait-for-exit (process)
  "Wait for PROCESS status to go to 'exit."
  (while (not (eq (process-status process) 'exit))
    (sleep-for 1)))


;; TODO: handle errors better than messaging
(defun emnode--child-process-sentinel (process status)
  "A sentinel for Emnode child PROCESS.

Emnode child processes are just Emacs asynchronous processes that
send their output to an Emnode HTTP connection.

The main job of this sentinel is to monitor when the STATUS of
PROCESS indicates the end of the PROCESS and to do
`emnode-http-end' on the associated HTTP connection when that
happens."
  (cond
   ((equal status "finished\n")
    (let ((httpcon (process-get process :emnode-httpcon)))
      (emnode-error
       "Emnode-child-process-sentinel Status @ finished: %s -> %s on %s"
       (process-status httpcon)
       (process-status process)
       httpcon)
      (if (not (eq 'closed (process-status httpcon)))
          (progn
            (emnode-http-send-string httpcon  "")
            (process-send-string httpcon "\r\n")
            (emnode--http-end httpcon)))))
   ((string-match "exited abnormally with code \\([0-9]+\\)\n" status)
    (let ((httpcon (process-get process :emnode-httpcon)))
      (emnode-error "Emnode-child-process-sentinel: %s on %s" status httpcon)
      (if (not (eq 'closed (process-status httpcon)))
          (progn
            (emnode-http-send-string httpcon "")
            (process-send-string httpcon "\r\n")
            (emnode--http-end httpcon)))
      (delete-process process)
      (kill-buffer (process-buffer process))))
   (t
    (emnode-error "Emnode-chlild-process-sentinel: %s on %s" status process))))

(defun emnode--child-process-filter (process data)
  "A generic filter function for emnode child processes.

emnode child processes are just emacs asynchronous processes that
send their output to an emnode http connection.

This filter function does the job of taking the output from the
async process and finding the associated emnode http connection
and sending the data there."
  (let ((httpcon (process-get process :emnode-httpcon)))
    (emnode-error
     "Emnode-child-process-filter http state: %s data length: %s on %s"
     (process-status httpcon)
     (length data)
     httpcon)
    (if (not (eq 'closed (process-status httpcon)))
        (emnode-http-send-string httpcon data))))

(defun emnode-child-process (httpcon program &rest args)
  "Run the specified PROGRAM asynchronously sending output to HTTPCON.

PROGRAM is the path to the program to run, to be resolved by
`start-process' in the usual way.

ARGS is a list of arguments to pass to the program.

It is NOT POSSIBLE to run more than one process at a time
directed at the same http connection."
  (let* ((args `(,(format "%s-%s" (process-name httpcon) program)
                 ,(format " %s-%s" (process-name httpcon) program)
                 ,program
                 ,@args
                ))
         (p (let ((process-connection-type nil))
              (apply 'start-process args))))
    (set-process-coding-system p 'raw-text-unix)
    ;; Bind the http connection to the process
    (process-put p :emnode-httpcon httpcon)
    ;; Bind the process to the http connection
    ;;
    ;; WARNING: this means you can only have 1 child process at a time
    (process-put httpcon :emnode-child-process p)
    ;; Setup the filter and the sentinel to do the right thing with
    ;; incomming data and signals
    (set-process-filter p 'emnode--child-process-filter)
    (set-process-sentinel p 'emnode--child-process-sentinel)
    (emnode-error "Emnode-child-process init %s" httpcon)))


;; File management

(defcustom emnode-send-file-program "/bin/cat"
  "The program to use for sending files.

Altering this is not recomended but it may be a good hook for
certain types of debugging."
  :group 'emnode
  :type '(string))

(defun emnode--buffer-template (file-buf replacements)
  "Template render a buffer and return a copy.

FILE-BUF is the source buffer to use, template sections marked up like:

 <!##E \\(.*?\\) E##!>

will be replaced with a value looked up in REPLACEMENTS.

REPLACEMENTS is either a hashtable or an association list.

For example:

 <title><!##E my-title E##!></title>
 <p>By <!##E my-name E##!>.</p>

with the REPLACEMENTS being:

  my-title => All things Emnode!
  my-name => Nic Ferrier

would result in the string:

  <title>All things Emnode!</title>
  <p>By Nic Ferrier</p>

being returned."
  (with-current-buffer file-buf
    (replace-regexp-in-string
     "<!##E \\(.*?\\) E##!>"
     (lambda (matched)
       (let ((match-var (match-string-no-properties 1 matched)))
         (cond
           ((hash-table-p replacements)
            (gethash match-var replacements ""))
           (t
            ;; Presume it's an alist
            (or
             (assoc-default match-var replacements nil t)
             "")))))
     (buffer-substring-no-properties (point-min)(point-max)))))

(defvar emnode-webserver-visit-file nil
  "Whether the webserver reads files by visiting buffers or not.

When set to `t' files to be sent with the `emnode-send-file' are
read into Emacs using `find-file'.")

(defvar emnode-replacements-httpcon nil
  "This is bound by `emnode-send-file' when doing replacements.

It should not be used otherwise.")

(defvar emnode-replacements-targetfile nil
  "This is bound by `emnode-send-file' when doing replacements.

It should not be used otherwise.")

(defun* emnode-send-file (httpcon targetfile
                                  &key
                                  preamble
                                  mime-types
                                  replacements)
  "Send the TARGETFILE to the HTTPCON.

If the TARGETFILE is relative then resolve it via the current
`load-file-name' or `buffer-file-name' or `default-directory'.

WARNING: this resolution order is likely to change because,
especially when developing `default-directory' can be quite
random (change buffer, change `default-directory').

Optionally you may specify extra keyword arguments:t

:PREAMBLE a string of data to send before the file.

:PREAMBLE is most useful for prefixing syntax to some other file,
for example you could prefix an XML file with XSL transformation
statements so a compliant user-agent will transform the XML.

:MIME-TYPES is an optional alist of MIME type mappings to help
resolve the type of a file.

If :REPLACEMENTS is specified it should be a hash-table or an
association list used to supply values for templating.  When
templating is specified the targetfile is not sent directly but
opened in Emacs as a buffer and transformed through the
templating system before being sent.  See
`emnode--buffer-template' for details of templating.

REPLACEMENTS can optionally be a function in which case the
return value is expected to be the hash-table or alist for the
variables.  The function should have no arguments but two
variables are bound during the function's execution
`emnode-replacements-httpcon' is the `httpcon' and
`emnode-replacements-targetfile' is the targetfile to be
delivered."
  (let ((filename
         (if (not (file-name-absolute-p targetfile))
             (file-relative-name
              targetfile
              (let ((dir (or load-file-name buffer-file-name)))
                (if dir
                    (directory-file-name dir)
                  default-directory)))
           targetfile)))
    (if (not (file-exists-p filename))
        ;; FIXME: This needs improving so we can handle the 404
        ;; This function should raise an exception?
        (emnode-send-404 httpcon)
      (let ((mimetype
             (or (when (listp mime-types)
                   (car (rassoc
                         (file-name-extension targetfile)
                         mime-types)))
                 (mm-default-file-encoding targetfile)
                  "application/octet-stream")))
        (emnode-http-start httpcon 200 `("Content-type" . ,mimetype))
        (when preamble (emnode-http-send-string httpcon preamble))
        (if (or emnode-webserver-visit-file replacements)
            (let ((file-buf (find-file-noselect filename)))
              (emnode-http-return
               httpcon
               (emnode--buffer-template
                file-buf
                ;; Replacements handling
                (if (functionp replacements)
                    (let ((emnode-replacements-httpcon httpcon)
                          (emnode-replacements-targetfile targetfile))
                      (funcall replacements))
                    replacements))))
            (emnode-child-process
             httpcon
             emnode-send-file-program
             (expand-file-name targetfile)))))))

(defmacro emnode-method (httpcon &rest method-mappings)
  "Map the HTTP method.

Write code like this:

 (emnode-method
  (GET
   (code)
   (more code))
  (POST
   (different code)
   (evenmorecode)))"
  (declare
   (debug (sexp &rest (sexp &rest form)))
   (indent 1))
  (let* ((var (make-symbol "v"))
         (conv (make-symbol "con")))
     `(let* ((,conv ,httpcon)
             (,var (intern (emnode-http-method ,conv))))
       (cond
        ,@(loop
           for d in method-mappings
           collect `((eq ,var (quote ,(car d)))
                     ,@(cdr d)))
        ;; If we don't map then send an error
        ;;
        ;; probably should be 405
        (t
         (emnode-send-500 ,conv))))))


;; Make simple handlers automatically

(defun emnode-make-redirecter (location &optional type)
  "Make a handler that will redirect to LOCATION.

Optionally, use the specified TYPE as the status code, eg:

 (emnode-make-redirect \"http://somehost.com/\" 301)"
  (lambda (httpcon)
    (emnode-send-redirect httpcon location type)))

(defun* emnode-make-send-file  (filename
                                &key
                                preamble
                                mime-types
                                replacements)
  "Make a handler that will serve a single FILENAME.

If the FILENAME is relative then it is resolved against the
package's `load-file-name'.

Optionally MIME-TYPES and other additional keyword arguments may be
specified and are passed through, see `emnode-send-file' for
details.

The REPLACEMENTS parameter can be a function that returns a
hash-table or alist, this is very useful for this function
because it allows dynamic variables to be defined.  Again, see
`emnode-send-file' for full documentation of this feature."
  (lambda (httpcon)
    (emnode-send-file
     httpcon
     filename
     :mime-types mime-types
     :preamble preamble
     :replacements replacements)))


;; Docroot protection

(defun emnode--under-docroot-p (target-file doc-root &optional ignore-missing)
  "Is the TARGET-FILE under the DOC-ROOT?
Optional argument IGNORE-MISSING will inhibit checks for missing files."
  (let ((docroot
         (directory-file-name
          (expand-file-name doc-root))))
    (and
     (string-match
      (format "^%s\\($\\|/\\)" docroot)
      target-file)
     (or ignore-missing (file-exists-p target-file)))))


(defun emnode-not-found (httpcon target-file)
  "`emnode-docroot-for' calls this when the doc was not found.

You can override this in tests to have interesting effects.  By
default it just calls `emnode-send-404'."
  (emnode-send-404 httpcon))

(defun emnode-cached-p (httpcon target-file)
  "Is the specified TARGET-FILE older than the HTTPCON?"
  (let ((modified-since
         (emnode-http-header httpcon 'if-modified-since :time)))
    (and
     modified-since
     (time-less-p
      (elt (file-attributes target-file) 5)
      modified-since))))

(defun emnode-cached (httpcon)
  "`emnode-docroot-for' calls this when the resources was cached.

By default it just calls `emnode-send-status' with 304."
  (emnode-send-status httpcon 304))

(defvar emnode-docroot-for-no-404 nil
  "When set to true `emnode-docroot-for' doesn't check for missing files.")

(defvar emnode-docroot-for-no-cache nil
  "When set to true `emnode-docroot-for' doesn't check for cached files.")

(defmacro emnode-docroot-for (doc-root with target-file-var
                                       on httpcon
                                       do &rest handling)
  "Docroot protection for Emnode handlers.

Test the path requested in HTTPCON is safely under the DOC-ROOT
specified, bind the TARGET-FILE-VAR to the resulting expanded
file name and execute the HANDLING code.

For example:

  (emnode-docroot-for
        \"~/work\"
        with file-var
        on httpcon
        do
        (emnode-send-file httpcon file-var))

checks any resource requested in HTTPCON is a file under the
doc-root \"~/work\" and if it is, binds the resulting file name
to FILE-VAR and calls the code following DO (which sends the file
to the HTTPCON).

When a file is not found (or not safe to return) `emnode-not-found' is called.

When a file is cached on the client (when a client sends a
conditional GET for the file that shows the client has an up to
date copy) then `emnode-cached' is called."
  (declare
   (debug (sexp "with" sexp "on" sexp "do" &rest form))
   (indent defun))
  (let ((dr (make-symbol "docroot"))
        (con (make-symbol "httpcon")))
    (assert (or (eq with 'with) (eq with :with)))
    (assert (or (eq on 'on)     (eq on :on)))
    (assert (or (eq do 'do)     (eq do :do)))
    `(let ((,dr ,doc-root)
           (,con ,httpcon))
       (let ((,target-file-var (emnode-get-targetfile ,con ,dr)))
         (if (not (emnode--under-docroot-p ,target-file-var ,dr
                                           emnode-docroot-for-no-404))
             (emnode-not-found ,con ,target-file-var)
           (if (and (not emnode-docroot-for-no-cache)
                    (emnode-cached-p ,con ,target-file-var))
               (emnode-cached ,con)
             ,@handling))))))


;; Webserver stuff

;;;###autoload
(defconst emnode-config-directory
  (expand-file-name (concat user-emacs-directory "emnode/"))
  "The config directory for emnode to store peripheral files.

This is used as a base for other constant directory or file
names (the emnode auth database is a file in this directory, the
emnode webserver has a docroot directory in this directory).

It is based on the `user-emacs-directory' which always seems to
be set, even when emacs is started with -Q.")

(defconst emnode-webserver-docroot-default
  (expand-file-name (concat emnode-config-directory "public_html/"))
  "The default location of the website.

This is used to detect whether emnode needs to create this
directory or not.")

(defcustom emnode-webserver-docroot
  emnode-webserver-docroot-default
  "The document root of the webserver.

Webserver functions are free to use this or not.  The
`emnode-webserver' function does use it."
  :group 'emnode
  :type 'file)

(defcustom emnode-webserver-extra-mimetypes
  '(("text/plain" . "creole")
    ("text/plain" . "el"))
  "Extra mime types to identify special file types.

This is just a way of hacking the mime type discovery so we can
add more file mappings more easily than editing `/etc/mime.types'."
  :group 'emnode
  :type '(alist :key-type string
                :value-type string))

(defcustom emnode-webserver-index '("index.html" "index.htm")
  "A list of possible index filenames.

Anyone of the values of this list may be picked as the index page
for a directory."
  :group 'emnode
  :type '(repeat string))

(defun emnode--webserver-setup ()
  "Setup the Emnode webserver by making a default public_html dir.

The server has a single `test.html' file, this is so we can show
off the standard webserver indexing in emnode's webserver."
  (emnode--dir-setup emnode-webserver-docroot
                     emnode-webserver-docroot-default
                     "default-webserver-test.html"
                     "test.html"
                     "default-webserver-image.png"))

(defun emnode-url-encode-path (path)
  "Return a url encoded version of PATH.

This is like `url-hexify-string' but it handles the parts of the
PATH properly.  It also hexifies single quote."
  (replace-regexp-in-string
   "'" "%27"
   (mapconcat
    'identity
    (loop
       for part in (split-string path "/")
       collect
         (concat
          (url-hexify-string part)))
    "/")))

(defcustom emnode-webserver-index-page-template "<html>
 <head>
  <title>%s</title>
 </head>
 <body>
  <h1>%s</h1>
  <div>%s</div>
 </body>
</html>
"
  "The page template used to render an index page.

The order of the variables is:

- the title of the document
- the title of the document
- the HTML formatted list of files."
  :group 'emnode
  :type '(string))

(defcustom emnode-webserver-index-file-template "<a href='%s'>%s</a><br/>\r\n"
  "The template for each file in the webserver index.

This is used to display each file in an automated directory index.

It is expected the template has 2 %s variables in it, the first
is the url to link to and the second is the content of the link."
  :group 'emnode
  :type '(string))

(defun emnode--webserver-index (docroot targetfile pathinfo &optional match)
  "Constructs index documents.

The index is made for the DOCROOT and TARGETFILE. The web path is
PATHINFO.

Optional MATCH is passed directly through to
`directory-files-and-attributes'."
  ;; TODO make this usable by people generally
  (let ((dirlist (directory-files-and-attributes targetfile nil match)))
    ;; TODO make some templating here so people can change this
    (format
     emnode-webserver-index-page-template
     pathinfo
     pathinfo
     (loop for dir-entry in dirlist
           concat
           (let ((entry
                  (format
                   "%s/%s"
                   (if (equal pathinfo "/")  "" pathinfo)
                   (car dir-entry))))
             (format
              emnode-webserver-index-file-template
              (emnode-url-encode-path entry)
              (car dir-entry)))))))

;;;###autoload
(defun emnode--webserver-handler-proc (httpcon docroot mime-types)
  "Actual webserver implementation.

Do webserving to HTTPCON from the DOCROOT using the MIME-TYPES
for meta information.

This is not a real handler (because it takes more than the
HTTPCON) but it is called directly by the real webserver
handlers."
  (emnode-docroot-for docroot
    with targetfile
    on httpcon
    do
    (let ((pathinfo (emnode-http-pathinfo httpcon)))
      (if (file-directory-p targetfile)
          ;; Use an existing index file or send a directory index
          (let* ((indexfile
                  (loop for i in emnode-webserver-index
                        if (member i (directory-files targetfile))
                        return i)))
            (if indexfile
                (emnode-send-file httpcon (concat targetfile "/" indexfile))
              (let ((index (emnode--webserver-index
                            docroot
                            targetfile
                            pathinfo)))
                (emnode-http-start httpcon 200 '("Content-type" . "text/html"))
                (emnode-http-return httpcon index))))
        ;; Send a file.
        (emnode-send-file
         httpcon
         targetfile
         :mime-types mime-types)))))

(defun emnode-webserver-handler-maker (&optional docroot extra-mime-types)
  "Make a webserver handler possibly with the DOCROOT and EXTRA-MIME-TYPES.

Returns a proc which is the handler. The handler serves files out
of the docroot and marks them with the content types that Emacs
knows about. You can add extra content types for the webserver
just by supplying an alist of mime-types and extensions for
EXTRA-MIME-TYPES.

The webserver handler also creates file indexes.

The webserver uses `emnode-test-path' to make sure that the
request does not go above the DOCROOT."
  (let ((my-docroot (or docroot emnode-webserver-docroot))
        (my-mime-types (or extra-mime-types
                           emnode-webserver-extra-mimetypes)))
    (lambda (httpcon)
      (emnode--webserver-handler-proc
       httpcon my-docroot my-mime-types))))


(defvar emnode--make-webserver-store nil
  "Alist of webservers made by `emnode-make-webserver'.

Stored as `docroot' . `webserver'.")

;;;###autoload
(defun emnode-make-webserver (docroot port)
  "Make a webserver interactively, for DOCROOT on PORT.

An easy way for a user to make a webserver for a particular
directory."
  (interactive "DServe files from: \nnTCP Port (try something over 8000):")
  (let ((webserver-proc (emnode-webserver-handler-maker docroot)))
    (add-to-list
     'emnode--make-webserver-store
     (cons docroot webserver-proc))
    (emnode-start webserver-proc :port port)))

;;;###autoload
(defun emnode-webserver (httpcon)
  "A simple webserver that serves documents out of `emnode-webserver-docroot'.

This is just an example of an emnode webserver, but it may be all
that is needed most of the time.

See `emnode-webserver-handler-maker' for more possibilities for
making webserver functions.

HTTPCON is the HTTP connection to the user agent."
  (emnode--webserver-setup)
  (let (use-webserver-handler-maker)
    (if use-webserver-handler-maker
        (emnode--webserver-handler-proc
         httpcon
         emnode-webserver-docroot
         emnode-webserver-extra-mimetypes)
        ;; Otherwise DO use the handler maker...
        (let ((webserver (emnode-webserver-handler-maker
                          emnode-webserver-docroot
                          emnode-webserver-extra-mimetypes)))
          (funcall webserver httpcon)))))

;; Default emnode auth databases

(defconst emnode-auth-db-spec-default
  `(db-hash
    :filename
    ,(expand-file-name (concat emnode-config-directory "emnode-auth")))
  "The default emnode-auth-db specification.")

(defcustom emnode-auth-db-spec
  emnode-auth-db-spec-default
  "The `db' specification of where the auth db is."
  :group 'emnode
  :type '(list symbol symbol string))

(defvar emnode-auth-db
  (db-make emnode-auth-db-spec)
  "Authentication database.

This is the data structure storing hashed passwords against
username keys.

It is an emnode database which can be one of several
implementations.")

(defvar emnode-secret-key "secret"
  "Secret key used to hash secrets like passwords.")

(defun emnode--auth-make-hash (username password)
  "Hash the secret key and the USERNAME and PASSWORD."
  (sha1 (format "%s:%s:%s"
                emnode-secret-key
                username
                password)))

(defun emnode-auth-user-add (username password &optional auth-db)
  "Command to add a user to the internal authentication database.

With prefix-arg also request the authentication database variable
name.  The authentication database must exist.  By default the
main `emnode-auth-db' is used."
  (interactive
   (list (read-from-minibuffer "username: ")
         (read-passwd "password: ")
         (when current-prefix-arg
             (read-from-minibuffer
              "auth database variable: "
              "emnode-auth-db"
              ;; FIXME - would be great to have completion of variable
              ;; names here
              nil
              t))))
  (unless auth-db
    (setq auth-db 'emnode-auth-db))
  (db-put
   username
   (emnode--auth-make-hash username password)
   (symbol-value auth-db))
  (message "username is %s" username))


(defun* emnode-auth-user-p (username
                            password
                            &key
                            auth-test)
  "Does the AUTH-TEST pass?

The password is stored in the db hashed keyed by the USERNAME,
this looks up and tests the hash.

The AUTH-DB is an `db', by default it is
`emnode-auth-db'"
  (let ((token (emnode--auth-make-hash username password)))
    (equal token (funcall auth-test username))))


(defvar emnode-loggedin-db (make-hash-table :test 'equal)
  "Stores logins - authentication sessions.

See `emnode-auth-login' for how this is updated.")


(progn
  ;; Sets up the emnode auth errors
  (put 'emnode-auth-credentials
       'error-conditions
       '(error emnode emnode-auth emnode-auth-credentials))
  (put 'emnode-auth-credentials
       'error-message
       "Emnode authentication failed")

  ;; For failing cookies
  (put 'emnode-auth-token
       'error-conditions
       '(error emnode emnode-auth emnode-auth-token))
  (put 'emnode-auth-token
       'error-message
       "Emnode authentication failed"))

(defun* emnode-auth-login (username
                           password
                           &key
                           auth-test
                           (loggedin-db emnode-loggedin-db))
  "Log a user in.

Check the USERNAME and PASSWORD with `emnode-auth-user-p' and
then update `emnode-loggedin-db' with the username and the login
record.

Takes optional AUTH-DB which is the database variable to
use (which is `emnode-auth-db' by default) and LOGGEDIN-DB which
is the logged-in state database to use and which is
`emnode-loggedin-db' by default."
  ;; FIXME - pass in the test function
  (if (emnode-auth-user-p username password :auth-test auth-test)
      (let* ((rndstr (format "%d" (random)))
             (hash (sha1 (format "%s:%s:%s"
                                 username
                                 rndstr
                                 emnode-secret-key)))
             (user-record
              (list
               :user username
               :token rndstr
               :hash hash)))
        (puthash username user-record loggedin-db)
        hash)
      ;; Else it was bad so throw an error.
      (signal 'emnode-auth-credentials (list username password))))

(defun* emnode-auth-check-p (username
                             token
                             &key
                             (loggedin-db emnode-loggedin-db))
  "Check login status of the USERNAME against the hashed TOKEN.

Optionally use the LOGGEDIN-DB supplied.  By default this is
`emnode-loggedin-db'."
  (let ((record (gethash username loggedin-db)))
    (equal token (plist-get record :hash))))

(defun emnode-auth-cookie-decode (cookie-value)
  "Decode an encoded emnode auth COOKIE-VALUE."
  (when (string-match "\\(.*\\)::\\(.*\\)" cookie-value)
    (cons (match-string 1 cookie-value) (match-string 2 cookie-value))))

(defun* emnode-auth-cookie-check-p (httpcon
                                    &key
                                    (cookie-name "emnode-auth")
                                    (loggedin-db emnode-loggedin-db))
  "Check that the user is loggedin according to the cookie.

The name of the cookie can be supplied with :COOKIE-NAME - by
default is is \"emnode-auth\".

LOGGEDIN-DB can be a loggedin state database which is expected to
be a `db'.  By default it is `emnode-loggedin-db'."
  (let ((cookie-value (emnode-http-cookie httpcon cookie-name t)))
    (if (not (emnode-auth-cookie-decode (or cookie-value "")))
        (signal 'emnode-auth-token cookie-value)
        (let ((username (match-string 1 cookie-value))
              (token (match-string 2 cookie-value)))
          (emnode-auth-check-p username token :loggedin-db loggedin-db)))))

(defun* emnode-auth-cookie-check (httpcon
                                  &key
                                  (cookie-name "emnode-auth")
                                  (loggedin-db emnode-loggedin-db))
  "Signal on cookie failure.

See `emnode-auth-cookie-check-p' for more details."
  (unless (emnode-auth-cookie-check-p
           httpcon
           :cookie-name cookie-name
           :loggedin-db loggedin-db)
    ;; Not sure this is the correct token...
    (signal 'emnode-auth-token :not-logged-in)))

(defvar emnode-auth-httpcon nil
  "Dynamic scope variable for HTTP con while we auth.")

(defun* emnode-auth-http-login (httpcon
                                username password logged-in
                                &key
                                (cookie-name "emnodeauth")
                                auth-test
                                (loggedin-db emnode-loggedin-db))
  "Log the USERNAME in on the HTTPCON if PASSWORD is correct.

If authentication succeeds set the relevant cookie and redirect
the user to LOGGED-IN.

Actually uses `emnode-auth-login' to do the assertion.
`emnode-auth-credentials' is signaled by that if the assertion fails.

AUTH-DB is a database, by default `emnode-auth-db', it's passed
to `emnode-auth-login'."
  (let* ((emnode-auth-httpcon httpcon)
         (hash
          (emnode-auth-login
           username password
           :auth-test auth-test
           :loggedin-db loggedin-db)))
    (emnode-http-header-set
     httpcon
     (emnode-http-cookie-make
      cookie-name
      (format "%s::%s" username hash)
      :path "/"))
    (emnode-send-redirect httpcon (or logged-in "/"))))

(defcustom emnode-auth-login-page "<html>
<body>
<form method='POST' action='<!##E target E##!>'>
<input type='hidden' name='redirect' value='<!##E redirect E##!>'/>
username: <input type='text' name='username'/><br/>
password: <input type='password' name='password'/><br/>
<input type='submit' name='login'/>
</form>
</body>
</html>"
  "A standard login page, used by `emnode-auth-login-sender'."
  :group 'emnode
  :type '(string))

(defun emnode-auth-login-sender (httpcon target redirect)
  "Send the login page for auth to HTTPCON.

The login page will send it's authentication request to TARGET.

The authentication will include username, password AND REDIRECT,
which is the URL to redirect to when login is successful.

This function sends the contents of the custom variable
`emnode-auth-login-page' after templating it."
  (emnode-http-start httpcon 200 `("Content-type" . "text/html"))
  ;; It would be nice to support preambles... not sure how.
  ;;  (when preamble (emnode-http-send-string httpcon preamble))
  (emnode-http-return
   httpcon
   (with-temp-buffer
     (insert emnode-auth-login-page)
     (emnode--buffer-template
      (current-buffer)
      `(("target" . ,target)
        ("redirect" . ,redirect))))))

(defun* emnode-auth--login-handler (httpcon
                                    sender target
                                    &key
                                    auth-test ; assert not nil?
                                    (cookie-name "emnodeauth")
                                    (loggedin-db emnode-loggedin-db))
  "The implementation of the login handler for auth testing.

This is the handler that is mapped to /login/ (which is the
default login path) or whatever you want the login path to be.

SENDER is the function which will send the login page to the
user, it takes an HTTPCON.  It must send a 'username' and
'password' HTTP parameters to this handler.

TARGET is the path that will be used as the login handler
path (the path to call this handler)."
  (emnode-method httpcon
      (GET
       (let ((to (or
                  (emnode-http-param httpcon "redirect")
                  "/")))
         (funcall sender httpcon target to)))
    (POST
     (let ((username (emnode-http-param httpcon "username"))
           (password (emnode-http-param httpcon "password"))
           (logged-in (emnode-http-param httpcon "redirect")))
       (condition-case err
           (emnode-auth-http-login
            httpcon
            username password logged-in
            :auth-test auth-test
            :cookie-name cookie-name)
         (emnode-auth-credentials
          (emnode-send-redirect
           httpcon
           (if (not logged-in)
               target
               (format "%s?redirect=%s" target logged-in))))
         (t (emnode-error
             "emnode-auth--login-handler: unexpected error: %S"
             err)))))))

(defun emnode-auth-default-test (username database)
  "The default test function used for Emnode auth."
  (db-get username database))

(defun* emnode-auth--make-login-handler
    (&key
     (sender 'emnode-auth-login-sender)
     (target "/login/")
     auth-test
     (auth-db emnode-auth-db) ; only used if the auth-test is not present
     (cookie-name "emnodeauth")
     (loggedin-db emnode-loggedin-db))
  "Make an `emnode-auth--login-handler', binding parameters."
  (lambda (httpcon)
    (emnode-auth--login-handler
     httpcon
     sender target
     ;; Make a test function if we don't have one
     :auth-test (if (functionp auth-test)
                    auth-test
                    (lambda (username)
                      (emnode-auth-default-test username auth-db)))
     :cookie-name cookie-name
     :loggedin-db loggedin-db)))

(defun* emnode-defauth (scheme-name
                        &key
                        (test :cookie)
                        auth-test
                        (auth-db 'emnode-auth-db)
                        (cookie-name "emnodeauth")
                        (failure-type :redirect)
                        (redirect "/login/")
                        (sender 'emnode-auth-login-sender))
  "Define an Emnode authentication scheme.

An authentication scheme consists of the following attributes:

TEST what sort of test is used to test the authentication, by
default this is `:cookie'.  No other authentication tests are
possible right now but in the future there might be many (there
might also be a general `:function' test that allows calling of a
function to implement the test).

COOKIE-NAME is used when the TEST is `:cookie'.  It is the name
of the cookie to use for authentication.  By default this is
`emnode-auth'.  It must be specified as a string.

AUTH-DB is the `db' used for authentication information.
It is used as the authority of information on users.  By default
this is `emnode-auth-db'.

AUTH-TEST is a function to implement retrieval of users.  It is
used in preference to AUTH-DB but can be nil in which case a
default based on AUTH-DB will be used.

FAILURE-TYPE is what to do if authentication fails.  Currently
only `:redirect' is supported.  To redirect on failure means to
send a 302 with a location to visit a login page.  :FAILURE-TYPE
is `:redirect' by default.

REDIRECT is where to redirect to if FAILURE-TYPE is `:redirect'.
By default this is \"/login/\".  If SENDER is not nil then a
dispatcher told about this auth scheme will dispatch a path
naming REDIRECT to SENDER.

SENDER is an Emnode handler taking additional parameters of
`target' and `redirect'.  By default this is the function
`emnode-auth-login-sender'.  Specify a different function if you
want to totally change the login page."
  (let* ((login-handler (emnode-auth--make-login-handler
                         :sender sender
                         :target redirect
                         :auth-test auth-test
                         :auth-db auth-db
                         :cookie-name cookie-name))
         (auth-scheme (list
                       :test test
                       :cookie-name cookie-name
                       :failure-type failure-type
                       :redirect redirect
                       :login-handler login-handler)))
    (puthash scheme-name
             auth-scheme
             emnode--defined-authentication-schemes)))

(defmacro emnode-auth-dispatcher (httpcon auth-scheme &rest body)
  "Dispatch HTTPCON to AUTH-SCHEME's handler if it matches.

Otherwise do BODY."
  (declare
   (debug (sexp sexp &rest form))
   (indent 2))
  (let ((httpcon-v (make-symbol "httpcon-v"))
        (auth-scheme-v (make-symbol "auth-scheme-v"))
        (redirect-v (make-symbol "redirect-v"))
        (handler-v (make-symbol "handler-v")))
    `(let* ((,httpcon-v ,httpcon)
            (,auth-scheme-v
             (gethash
              ,auth-scheme
              emnode--defined-authentication-schemes))
            (,redirect-v (plist-get ,auth-scheme-v :redirect))
            (,handler-v (plist-get ,auth-scheme-v :login-handler)))
       (if (emnode--mapper-find-match-func
            (emnode-http-pathinfo ,httpcon-v)
            (cons ,redirect-v ,handler-v))
           ;; If the current path matches call the auth handler
           (funcall ,handler-v ,httpcon-v)
           ;; Else do whatever the body was
           ,@body))))

(defmacro if-emnode-auth (httpcon scheme authd &rest anonymous)
  "Check the HTTPCON for SCHEME auth and eval AUTHD.

If the auth fails then evaluate ANONYMOUS instead."
  (declare
   (debug (sexp sexp sexp &rest form))
   (indent 2))
  (let ((httpconv (make-symbol "httpconv")))
    `(let ((,httpconv ,httpcon)
           (scheme-list
            (gethash ,scheme
                     emnode--defined-authentication-schemes)))
       (if (eq :cookie (plist-get scheme-list :test))
           (condition-case token
               (progn
                 (emnode-auth-cookie-check
                  ,httpconv
                  :cookie-name (plist-get scheme-list :cookie-name))
                 ;; Do whatever the code was now.
                 ,authd)
             ;; On auth failure do the ELSE
             (emnode-auth-token
              (progn ,@anonymous)))
           ;; Not a cookie test - not sure what to do...
           (message "EMNODE AUTH IF - NOT COOKIE!")))))

(defmacro with-emnode-auth (httpcon scheme &rest body)
  "Protect code with authentication using HTTPCON and SCHEME.

This macro protects code in a handler with a check for an
authenticated request (the check is configurable).  If the check
fails then an appropriate action is taken; for example, sending a
login page.

SCHEME is the authentication scheme to use as defined by
`emnode-auth-define-scheme'."
  (declare
   (debug (sexp sexp &rest form))
   (indent 2))
  (let ((httpconv (make-symbol "httpconv")))
    `(let ((,httpconv ,httpcon))
       (if-emnode-auth ,httpconv ,scheme
         ,@body
         (let ((to
                (cond
                  (;; We have a wrapper... other lists other
                   ;; than wrappers are probably possible; we
                   ;; should qualify the test here to be
                   ;; wrapper specific
                   (listp (plist-get scheme-list :redirect))
                   (format
                    "%s?redirect=%s"
                    (elt (plist-get scheme-list :redirect) 3)
                    (emnode-http-pathinfo ,httpconv)))
                  ;; A plain string can be used directly
                  ((stringp (plist-get scheme-list :redirect))
                   (plist-get scheme-list :redirect))
                  (t
                   (error
                    ":redirect MUST be  a list or a string")))))
           (emnode-send-redirect ,httpconv to))))))

(defun emnode-test-login (auth target username password)
  "Send a test login to Emnode."
  ;; FIXME - use AUTH as a reference to an emnode-authentication
  ;; declaration and pull things like /login/ from it
  (emnode-test-call
   (format "/login/?redirect=%s" target)
   :method "POST"
   :parameters (list (cons "username" username)
                     (cons "password" password))))

;;; Main customization stuff

(defcustom emnode-init-port 8000
  "The port that `emnode-init' starts the default server on."
  :group 'emnode)

(defcustom emnode-init-host "localhost"
  "The host that `emnode-init' starts the default server listening on."
  :group 'emnode)

;;;###autoload
(defun emnode-init ()
  "Bootstraps the emnode environment when the Lisp is loaded.

It's useful to have emnode start automatically... on Lisp
load.  If the variable `emnode-init-port' is set then this
function will launch a server on it.

The server is started with `emnode-hostpath-default-handler' as
the handler and listening on `emnode-init-host'"
  (interactive)
  (if emnode-init-port
      (condition-case nil
          (emnode-start
           'emnode-hostpath-default-handler
           :port emnode-init-port
           :host emnode-init-host)
        (error
         (emnode-error
          "emnode-init: can't start - port %d has something attached already"
          emnode-init-port))))
  ;; Turn on the defer queue processor if we need to
  (if emnode-defer-on
      (if (not emnode--defer-timer)
          (emnode--init-deferring))))

;;;###autoload
(defcustom emnode-do-init 't
  "Should emnode start a server on load?

The server that is started is controlled by more emnode
customizations.

`emnode-hostpath-default-table' defines the mappings from
hostpath regexs to handler functions. By default emnode ships
with this customization setup to serve the document root defined
in `emnode-webserver-docroot', which by default is ~/public_html."
  :group 'emnode
  :type '(boolean)
  )

(defvar emnode--inited nil
  "Records when emnode is initialized.
This is autoloading mechanics, see the eval-after-load for doing init.")

;; Auto start emnode if we're ever loaded
;;;###autoload
(eval-after-load 'emnode
  (if (and (boundp 'emnode-do-init)
           emnode-do-init
	   (or (not (boundp 'emnode--inited))
	       (not emnode--inited)))
      (progn
        (emnode-init)
        (setq emnode--inited nil))))

(provide 'emnode)

;;; emnode.el ends here
