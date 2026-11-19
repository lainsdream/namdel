;;;; namdel.lisp -- namdel protocol server
;;;; Socket/thread-per-client/HTTP parsing scaffold taken from web.lisp.
;;;; Start with: sbcl --load namdel.lisp
;;;;
;;;; PROTOCOL:
;;;;  - nickname + birthdate -> public address ("who to send to").
;;;;  - time -> private room-ownership secret, claimed EXACTLY ONCE.
;;;;    Lost -> unrecoverable forever.
;;;;  - room = (nickname . birthdate). First entrant with any `time`
;;;;    becomes the active owner; later attempts create "shadow" rooms
;;;;    that are never served and never flagged as invalid (indistinguishable
;;;;    from the outside).
;;;;  - pending[to] -- packets sitting on the server until the recipient
;;;;    fetches and confirms them (/ack).
;;;;  - Persistence is permanent: rooms and pending packets never expire.
;;;;    How many unanswered packets to tolerate is entirely up to the
;;;;    receiving client; the server has no notion of it.
;;;;  - True drop: client explicitly confirms via /ack that a packet was
;;;;    handled (stored locally OR knowingly rejected) -- server erases it
;;;;    physically, without recording which outcome it was.
;;;;
;;;; Minimum for LispPad tests: /send, /inbox, /ack. Nothing else.
;;;; Persisted to disk as plain s-expressions, one directory per room:
;;;;   rooms/<hash>/settings.txt -- nickname, birthdate, secret-hash,
;;;;     created-at. Write-once: set at room creation, never touched again.
;;;;   rooms/<hash>/packets.txt  -- pending list, rewritten on every
;;;;     /send and /ack.
;;;; All rooms are loaded back into *rooms* once at startup.

;;; ---------------------------------------------------------------------
;;; State (in-memory cache; disk in rooms/ is the source of truth)
;;; ---------------------------------------------------------------------

;;; rsync -avz -e "ssh -i ~/.ssh/selectel_namdel" /path/to/local/public/ root@139.100.220.230:/root/public/
(ql:quickload '(:ironclad :cl-base64))

(defstruct nam-room
  nickname
  birthdate
  secret-hash        ; hash of the active owner's `time`
  created-at
  pending)           ; list of (:from :time :text) plists awaiting ack

;; key: (cons nickname birthdate) as string "nickname|birthdate"
(defvar *rooms* (make-hash-table :test 'equal))
(defvar *rooms-lock* (sb-thread:make-mutex :name "rooms"))
(defparameter *public-dir* #P"/root/public/")

;;; ---------------------------------------------------------------------
;;; Utilities
;;; ---------------------------------------------------------------------

(defun room-key (nickname birthdate)
  (concatenate 'string nickname "|" birthdate))

(defun simple-hash (str)
  "Non-cryptographic hash for the prototype -- swap for sha256 (ironclad)
   before anything beyond a pet test; only the mechanics matter here."
  (sxhash str))

(defun now ()
  (get-universal-time))

(defun content-type-for (path)
  (let ((ext (pathname-type path)))
    (cond
      ((string= ext "html") "text/html; charset=utf-8")
      ((string= ext "js")   "application/javascript; charset=utf-8")
      ((string= ext "svg")  "image/svg+xml")
      ((string= ext "edn")  "text/plain; charset=utf-8")
      ((string= ext "css")  "text/css; charset=utf-8")
      (t "application/octet-stream"))))

(defun serve-static-file (stream request-path)
  (let* ((rel-path (string-left-trim "/" request-path))
         (full-path (merge-pathnames rel-path *public-dir*))
         (ext (pathname-type full-path)))
    (cond
      ((not (probe-file full-path))
       (write-http-response stream "404 Not Found" "text/plain; charset=utf-8" "not found"))
      ((member ext '("woff" "woff2" "ttf" "otf" "eot" "png" "ico") :test #'string=)
       (write-http-response-binary stream "200 OK" (content-type-for full-path)
                                   (read-file-bytes full-path)))
      (t
       (write-http-response stream "200 OK" (content-type-for full-path)
                            (uiop:read-file-string full-path))))))

;;; ---------------------------------------------------------------------
;;; I/O helpers (from web.lisp, mostly unchanged)
;;; ---------------------------------------------------------------------

;; Stream is always binary ((unsigned-byte 8)), see start(): Content-Length
;; is counted in BYTES, and a character stream reading Cyrillic UTF-8
;; (2 bytes/char) by length would hang waiting for bytes that never arrive.

(defun write-http-response (stream status content-type body)
  (let* ((header (format nil "HTTP/1.1 ~a~C~CContent-Type: ~a~C~CConnection: close~C~C~C~C"
                         status #\Return #\Linefeed content-type #\Return #\Linefeed
                         #\Return #\Linefeed #\Return #\Linefeed)))
    (write-sequence (sb-ext:string-to-octets header :external-format :ascii) stream)
    (write-sequence (sb-ext:string-to-octets body :external-format :utf-8) stream)
    (force-output stream)))

(defun write-http-response-binary (stream status content-type body-bytes)
  (let ((header (format nil "HTTP/1.1 ~a~C~CContent-Type: ~a~C~CConnection: close~C~C~C~C"
                        status #\Return #\Linefeed content-type #\Return #\Linefeed
                        #\Return #\Linefeed #\Return #\Linefeed)))
    (write-sequence (sb-ext:string-to-octets header :external-format :ascii) stream)
    (write-sequence body-bytes stream)
    (force-output stream)))

(defun read-file-bytes (path)
  (with-open-file (in path :element-type '(unsigned-byte 8))
    (let ((buf (make-array (file-length in) :element-type '(unsigned-byte 8))))
      (read-sequence buf in)
      buf)))

(defun read-http-line (stream)
  "Reads one CRLF/LF line from the binary stream as an ASCII string.
   HTTP headers and the request line are always ASCII; the body (which
   may be UTF-8) is read separately by read-body."
  (let ((bytes (make-array 0 :element-type '(unsigned-byte 8)
                             :adjustable t :fill-pointer 0)))
    (loop for b = (read-byte stream nil nil)
          while (and b (/= b 10))
          do (vector-push-extend b bytes)
          finally (return (if (and (null b) (zerop (length bytes)))
                              nil
                              (sb-ext:octets-to-string bytes :external-format :ascii))))))

(defun read-http-headers (stream)
  (loop for line = (read-http-line stream)
        while (and line (plusp (length (string-trim '(#\Return) line))))
        collect (let ((colon (position #\: line)))
                  (and colon
                       (cons (string-downcase (subseq line 0 colon))
                             (string-trim '(#\Space #\Tab #\Return)
                                          (subseq line (1+ colon))))))))

(defparameter +ws-guid+ "258EAFA5-E914-47DA-95CA-C5AB0DC85B11")

(defun ws-accept-key (client-key)
  (let* ((concatenated (concatenate 'string client-key +ws-guid+))
         (digest (ironclad:digest-sequence
                  :sha1
                  (sb-ext:string-to-octets concatenated :external-format :ascii))))
    (cl-base64:usb8-array-to-base64-string digest)))

(defun handle-websocket-upgrade (stream headers)
  (let ((ws-key (cdr (assoc "sec-websocket-key" headers :test #'string=))))
    (unless ws-key (return-from handle-websocket-upgrade nil))
    (let* ((accept-key (ws-accept-key ws-key))
           (response (format nil "HTTP/1.1 101 Switching Protocols~C~CUpgrade: websocket~C~CConnection: Upgrade~C~CSec-WebSocket-Accept: ~a~C~C~C~C"
                             #\Return #\Linefeed #\Return #\Linefeed #\Return #\Linefeed
                             accept-key #\Return #\Linefeed #\Return #\Linefeed)))
      (write-sequence (sb-ext:string-to-octets response :external-format :ascii) stream)
      (force-output stream)
      t)))

(defun read-ws-frame (stream)
  (flet ((rb () (read-byte stream nil nil)))
    (let ((b0 (rb)))
      (unless b0 (return-from read-ws-frame (values nil nil)))
      (let* ((opcode (logand b0 #x0f))
             (b1 (rb)))
        (unless b1 (return-from read-ws-frame (values nil nil)))
        (let* ((masked (logbitp 7 b1))
               (len (logand b1 #x7f)))
          (setf len
                (cond ((= len 126)
                       (let ((h (rb)) (l (rb)))
                         (unless (and h l) (return-from read-ws-frame (values nil nil)))
                         (logior (ash h 8) l)))
                      ((= len 127)
                       (loop with n = 0
                             for i from 7 downto 0
                             for byte = (rb)
                             do (unless byte (return-from read-ws-frame (values nil nil)))
                                (setf n (logior n (ash byte (* i 8))))
                             finally (return n)))
                      (t len)))
          (let ((mask-key (when masked
                            (let ((bytes (list (rb) (rb) (rb) (rb))))
                              (unless (every #'identity bytes)
                                (return-from read-ws-frame (values nil nil)))
                              (make-array 4 :element-type '(unsigned-byte 8) :initial-contents bytes))))
                (payload (make-array len :element-type '(unsigned-byte 8))))
            (let ((read (read-sequence payload stream)))
              (unless (= read len) (return-from read-ws-frame (values nil nil))))
            (when masked
              (dotimes (i len)
                (setf (aref payload i) (logxor (aref payload i) (aref mask-key (mod i 4))))))
            (values opcode payload)))))))

(defun write-ws-frame (stream opcode payload-bytes)
  (let ((len (length payload-bytes)))
    (write-byte (logior #x80 opcode) stream)
    (cond ((< len 126) (write-byte len stream))
          ((< len 65536)
           (write-byte 126 stream)
           (write-byte (ldb (byte 8 8) len) stream)
           (write-byte (ldb (byte 8 0) len) stream))
          (t (write-byte 127 stream)
             (loop for i from 7 downto 0
                   do (write-byte (ldb (byte 8 (* i 8)) len) stream))))
    (write-sequence payload-bytes stream)
    (force-output stream)))

(defun write-ws-text (stream string)
  (write-ws-frame stream #x1 (sb-ext:string-to-octets string :external-format :utf-8)))

(defun read-ws-text (stream)
  (loop
    (multiple-value-bind (opcode payload) (read-ws-frame stream)
      (cond
        ((null opcode) (return nil))
        ((= opcode #x8) (return nil))
        ((= opcode #x9) (write-ws-frame stream #xA payload))
        ((= opcode #xA))
        ((= opcode #x1) (return (sb-ext:octets-to-string payload :external-format :utf-8)))
        (t (return nil))))))

(defun alist-get (alist name)
  (cdr (assoc name alist :test #'string=)))

(defun read-body (stream headers &optional (max-len 8192))
  "Content-Length is in bytes: read exactly that many bytes, then decode as UTF-8."
  (let* ((length-text (alist-get headers "content-length"))
         (length (and length-text (parse-integer length-text :junk-allowed t))))
    (unless (and length (<= 0 length max-len))
      (error "Missing or unreasonable content-length"))
    (let ((bytes (make-array length :element-type '(unsigned-byte 8))))
      (read-sequence bytes stream)
      (sb-ext:octets-to-string bytes :external-format :utf-8))))

(defun parse-request-line (line)
  (let ((first-space (position #\Space line)))
    (when first-space
      (let ((second-space (position #\Space line :start (1+ first-space))))
        (when second-space
          (values (subseq line 0 first-space)
                  (subseq line (1+ first-space) second-space)))))))

(defun split-path-query (path)
  "Returns (values path-without-query query-alist)."
  (let ((qpos (position #\? path)))
    (if (null qpos)
        (values path nil)
        (values (subseq path 0 qpos)
                (loop for pair in (split-on-char (subseq path (1+ qpos)) #\&)
                      for eqpos = (position #\= pair)
                      when eqpos
                      collect (cons (subseq pair 0 eqpos) (subseq pair (1+ eqpos))))))))

(defun split-on-char (str ch)
  (loop with start = 0
        for pos = (position ch str :start start)
        collect (subseq str start pos)
        while pos
        do (setf start (1+ pos))))

;;; ---------------------------------------------------------------------
;;; Persistence (one directory per room; write-once settings + rewritten packets)
;;; ---------------------------------------------------------------------

(defvar *rooms-dir* "rooms/")

(defun room-dir (key)
  "Directory for a room, named by hash of its key -- avoids trusting
   nickname/birthdate (arbitrary client strings) as path components."
  (format nil "~a~x/" *rooms-dir* (sxhash key)))

(defun write-sexpr-file (path obj)
  (ensure-directories-exist path)
  (with-open-file (out path :direction :output
                            :if-exists :supersede :if-does-not-exist :create)
    (write obj :stream out)))

(defun read-sexpr-file (path)
  (with-open-file (in path) (read in)))

(defun save-room-settings! (r key)
  "Called once, at room creation -- never again (secret-hash is write-once)."
  (write-sexpr-file (concatenate 'string (room-dir key) "settings.txt")
                     (list :nickname (nam-room-nickname r)
                           :birthdate (nam-room-birthdate r)
                           :secret-hash (nam-room-secret-hash r)
                           :created-at (nam-room-created-at r))))

(defun save-room-packets! (r key)
  "Called on every /send and /ack for this room."
  (write-sexpr-file (concatenate 'string (room-dir key) "packets.txt")
                     (nam-room-pending r)))

(defun load-all-rooms! ()
  "Populates *rooms* from disk. Only runs when *rooms* is empty, so
   reloading this file at the REPL doesn't clobber live in-memory state
   with a stale snapshot."
  (when (and (zerop (hash-table-count *rooms*)) (probe-file *rooms-dir*))
    (dolist (dir (directory (merge-pathnames "*/" *rooms-dir*)))
      (let ((settings-path (merge-pathnames "settings.txt" dir))
            (packets-path (merge-pathnames "packets.txt" dir)))
        (when (probe-file settings-path)
          (let* ((settings (read-sexpr-file settings-path))
                 (nickname (getf settings :nickname))
                 (birthdate (getf settings :birthdate)))
            (setf (gethash (room-key nickname birthdate) *rooms*)
                  (make-nam-room :nickname nickname :birthdate birthdate
                                 :secret-hash (getf settings :secret-hash)
                                 :created-at (getf settings :created-at)
                                 :pending (and (probe-file packets-path)
                                              (read-sexpr-file packets-path))))))))
    (format t "namdel: loaded ~a room(s) from disk.~%" (hash-table-count *rooms*))))

;;; ---------------------------------------------------------------------
;;; Protocol logic
;;; ---------------------------------------------------------------------

(defun get-or-touch-room (nickname birthdate time)
  "Returns the room. First entrant under nickname+birthdate becomes the
   active owner. Existing owner is verified by secret-hash; a mismatch
   creates a 'shadow' room -- returns NIL, indistinguishable from outside."
  (sb-thread:with-mutex (*rooms-lock*)
    (let* ((key (room-key nickname birthdate))
           (existing (gethash key *rooms*))
           (hash (simple-hash time)))
      (cond
        ((null existing)
         (let ((r (make-nam-room :nickname nickname :birthdate birthdate
                                 :secret-hash hash :created-at (now) :pending nil)))
           (setf (gethash key *rooms*) r)
           (save-room-settings! r key)
           (save-room-packets! r key)
           r))
        ((= (nam-room-secret-hash existing) hash)
         existing)
        ;; secret mismatch -> shadow attempt; caller must behave as if the
        ;; room exists and is empty (silence, not an error)
        (t nil)))))

(defun deliver-packet! (to-nickname to-birthdate from text signed keywrap public-key)
  "Places a packet in the recipient's room. Returns :ok or :no-room.
   The unanswered-packet threshold/blackhole is client-side, not here."
  (sb-thread:with-mutex (*rooms-lock*)
    (let* ((key (room-key to-nickname to-birthdate))
           (r (gethash key *rooms*)))
      (cond
        ((null r) :no-room)
        (t
         (setf (nam-room-pending r)
               (append (nam-room-pending r)
                       (list (list :from from :time (now) :text text :signed signed :keywrap keywrap :public-key public-key))))
         (save-room-packets! r key)
         :ok)))))

(defun ack-packet! (nickname birthdate index)
  "Client confirms the packet at this index (0-based, /inbox order) was
   handled -- stored or knowingly rejected. Either way the server just
   erases it, without recording which outcome it was."
  (sb-thread:with-mutex (*rooms-lock*)
    (let* ((key (room-key nickname birthdate))
           (r (gethash key *rooms*)))
      (cond
        ((null r) :no-room)
        (t
         (let ((pending (nam-room-pending r)))
           (if (and (>= index 0) (< index (length pending)))
               (progn
                 (setf (nam-room-pending r)
                       (append (subseq pending 0 index)
                               (subseq pending (1+ index))))
                 (save-room-packets! r key)
                 :ok)
               :bad-index)))))))

(defvar *call-connections* (make-hash-table :test 'equal))
(defvar *call-connections-lock* (sb-thread:make-mutex :name "call-connections"))

(defun register-call-connection! (key stream)
  "Регистрирует STREAM, возвращает вытесненный старый поток или NIL."
  (sb-thread:with-mutex (*call-connections-lock*)
    (let ((old (gethash key *call-connections*)))
      (setf (gethash key *call-connections*) stream)
      (and old (not (eq old stream)) old))))

(defun unregister-call-connection! (key stream)
  (sb-thread:with-mutex (*call-connections-lock*)
    (when (eq (gethash key *call-connections*) stream)
      (remhash key *call-connections*))))

(defun route-call-event! (to-nickname to-birthdate event)
  (let ((target (sb-thread:with-mutex (*call-connections-lock*)
                  (gethash (room-key to-nickname to-birthdate) *call-connections*))))
    (if target
        (handler-case (progn (write-ws-text target (sexpr-wire event)) :ok)
          (error () :unavailable))
        :unavailable)))

(defun subscription-json (sub)
  (destructuring-bind (&key endpoint p256dh auth) sub
    (format nil "{\"endpoint\":\"~a\",\"keys\":{\"p256dh\":\"~a\",\"auth\":\"~a\"}}"
            endpoint p256dh auth)))

(defun home-file (name) (namestring (merge-pathnames name (user-homedir-pathname))))

(defparameter *push-python* (home-file "push-venv/bin/python3"))

(defun subscription-gone-p (error-output)
  (and error-output
       (>= (length error-output) 4)
       (string= "GONE" (subseq error-output 0 4))))

(defun send-push (from-nickname target-nickname target-birthdate)
  (let* ((key (room-key target-nickname target-birthdate))
         (sub (gethash key *subscriptions*)))
    (unless sub (return-from send-push (values nil "no subscription")))
    (multiple-value-bind (output error-output code)
        (uiop:run-program
         (list *push-python* (home-file "push.py") (subscription-json sub) from-nickname (home-file "vapid_private.pem"))
         :output '(:string :stripped t)
         :error-output '(:string :stripped t)
         :ignore-error-status t)
      (declare (ignore output))
      (cond
        ((zerop code) (values t nil))
        ((subscription-gone-p error-output)
         (remhash key *subscriptions*)
         (values nil "subscription gone, removed"))
        (t (values nil error-output))))))

(defun safe-read (s)
  (let ((*read-eval* nil))
    (read-from-string s)))

(defun call-ws-loop (stream)
  (let (key)
    (unwind-protect
         (handler-case
             (progn
               (let ((auth-msg (sb-ext:with-timeout 10 (read-ws-text stream))))
                 (unless auth-msg (return-from call-ws-loop))
                 (let* ((auth (safe-read auth-msg))
                        (nickname (first auth)) (birthdate (second auth)) (time (third auth)))
                   (unless (and (stringp nickname) (stringp birthdate) (stringp time))
                     (return-from call-ws-loop))
                   (unless (get-or-touch-room nickname birthdate time)
                     (return-from call-ws-loop))
                   (setf key (room-key nickname birthdate))
                   (register-call-connection! key stream)
                   (write-ws-text stream (sexpr-wire '(:ok)))
                   (loop
                     (let ((msg (read-ws-text stream)))
                       (unless msg (return))
                       (let* ((event (safe-read msg))
                              (etype (first event)))
                         (case etype
                           (:presence
                            (let* ((p-nick (second event)) (p-bd (third event)))
                              (when (and (stringp p-nick) (stringp p-bd))
                                (let ((online (sb-thread:with-mutex (*call-connections-lock*)
                                                (gethash (room-key p-nick p-bd) *call-connections*))))
                                  (write-ws-text stream
                                                 (sexpr-wire (if online '(:presence/online) '(:presence/offline))))
                                  (unless online
                                    (sb-thread:make-thread
                                     (lambda ()
                                       (multiple-value-bind (ok err) (send-push nickname p-nick p-bd)
                                         (unless ok (format t "send-push FAILED: ~a~%" err))))
                                     :name "push-notify"))))))
                           (:to
                            (let* ((to-nick (second event)) (to-bd (third event)) (payload (fifth event)))
                              (when (and (stringp to-nick) (stringp to-bd))
                                (when (eq (route-call-event! to-nick to-bd payload) :unavailable)
                                  (write-ws-text stream (sexpr-wire '(:call/unavailable))))))))))))))
           (sb-ext:timeout ()
             (format t "call-ws-loop: auth timeout~%"))
           (error (c)
             (format t "call-ws-loop error: ~a~%" c)))
      (when key (unregister-call-connection! key stream)))))

;;; ---------------------------------------------------------------------
;;; HTTP routes
;;; ---------------------------------------------------------------------

(defun respond-ok (stream body)
  (write-http-response stream "200 OK" "text/plain; charset=utf-8" body))

(defun respond-status (stream status)
  "Writes STATUS (a keyword symbol like :ok / :no-room) as a 200 s-expr reply."
  (respond-ok stream (prin1-to-string (string-downcase (symbol-name status)))))

(defun respond-error (stream condition)
  (write-http-response stream "400 Bad Request" "text/plain; charset=utf-8"
                       (prin1-to-string (format nil "~a" condition))))

(defun read-sexpr-body (stream headers)
  (safe-read (read-body stream headers)))

(defun handle-send (stream headers)
  (handler-case
      (let* ((fields (read-sexpr-body stream headers))
             (from (first fields))
             (from-bd (second fields))
             (from-time (third fields))
             (to (fourth fields))
             (to-bd (fifth fields))
             (text (sixth fields))
             (signed (seventh fields))
             (keywrap (eighth fields))
             (public-key (ninth fields)))
        (unless (and (stringp from) (stringp from-bd) (stringp from-time)
                     (stringp to) (stringp to-bd)
                     (member signed '(t nil))
                     (if (null text) (stringp keywrap) (stringp text)))
          (error "malformed send: expected (from from-bd from-time to to-bd text signed keywrap public-key)"))
        ;; confirms sender owns their own room, so no one can send "as" someone else
        (get-or-touch-room from from-bd from-time)
        (respond-status stream (deliver-packet! to to-bd from text signed keywrap public-key)))
    (error (c) (respond-error stream c))))

(defun sexpr-wire (obj)
  "prin1-to-string, but an empty list prints as \"()\" not \"NIL\" -- needed
   for the CL->Scheme bridge, since Scheme reads NIL as a symbol, not '()."
  (if (null obj) "()" (prin1-to-string obj)))

(defun handle-inbox (stream query)
  (handler-case
      (let* ((nickname (alist-get query "nickname"))
             (birthdate (alist-get query "birthdate"))
             (time (alist-get query "time")))
        (unless (and nickname birthdate time)
          (error "missing nickname/birthdate/time"))
        ;; shadow room (r = nil) -> empty inbox, same as an active-but-empty one
        (let ((r (get-or-touch-room nickname birthdate time)))
          (respond-ok stream
            (sexpr-wire (and r (loop for p in (nam-room-pending r)
                collect (list (getf p :from) (getf p :time) (getf p :text) (getf p :signed) (getf p :keywrap) (getf p :public-key))))))))
    (error (c) (respond-error stream c))))

(defun handle-ack (stream headers)
  (handler-case
      (let* ((fields (read-sexpr-body stream headers))
             (nickname (first fields))
             (birthdate (second fields))
             (index (third fields)))
        (unless (and (stringp nickname) (stringp birthdate) (integerp index))
          (error "malformed ack: expected (nickname birthdate index)"))
        (respond-status stream (ack-packet! nickname birthdate index)))
    (error (c) (respond-error stream c))))

(defvar *subscriptions* (make-hash-table :test 'equal))
(defvar *vapid-public-key* "BCO9JCiwoWGei3OfJZ9XGi9PZ209favlgZ9QCAakOofLBtJyK0xWwOcibpssD3_RUernQ2hHxGNTeHI57ypes5c")

(defun handle-push-subscribe (stream headers)
  (handler-case
      (destructuring-bind (nickname birthdate endpoint p256dh auth) (read-sexpr-body stream headers)
        (setf (gethash (room-key nickname birthdate) *subscriptions*)
              (list :endpoint endpoint :p256dh p256dh :auth auth))
        (write-http-response stream "200 OK" "text/plain; charset=utf-8" "ok"))
    (error (c)
      (write-http-response stream "400 Bad Request" "text/plain; charset=utf-8"
                           (format nil "bad request: ~a" c)))))

(defun handle-vapid-key (stream)
  (write-http-response stream "200 OK" "text/plain; charset=utf-8" *vapid-public-key*))

(defun handle-request (stream)
  (let ((line (or (read-http-line stream) "")))
    (multiple-value-bind (method full-path) (parse-request-line line)
      (let ((headers (read-http-headers stream)))
        (multiple-value-bind (path query) (split-path-query (or full-path ""))
          (cond
            ((and (string= method "GET") (string= path "/"))
             (write-http-response stream "200 OK" "text/plain; charset=utf-8" "healthy"))
            ((and (string= method "GET") (string= path "/app"))
             (serve-static-file stream "/index.html"))
            ((and (string= method "POST") (string= path "/send"))
             (handle-send stream headers))
            ((and (string= method "GET") (string= path "/inbox"))
             (handle-inbox stream query))
            ((and (string= method "POST") (string= path "/ack"))
             (handle-ack stream headers))
            ((and (string= method "GET") (string= path "/call-ws")
                  (assoc "upgrade" headers :test #'string=))
             (when (handle-websocket-upgrade stream headers)
               (call-ws-loop stream)))
            ((and (string= method "POST") (string= path "/push/subscribe"))
             (handle-push-subscribe stream headers))
            ((and (string= method "GET") (string= path "/push/vapid-key"))
             (handle-vapid-key stream))
            ((string= method "GET")
             (serve-static-file stream path))
            (t
             (write-http-response stream "404 Not Found" "text/plain; charset=utf-8" "Not found."))))))))

;;; ---------------------------------------------------------------------
;;; Socket server (from web.lisp, only the bind address changed)
;;; ---------------------------------------------------------------------

(defvar *server-socket* nil)
(defvar *accept-thread* nil)

(defun stop ()
  (when *server-socket*
    (ignore-errors (sb-bsd-sockets:socket-close *server-socket*))
    (setf *server-socket* nil))
  (when *accept-thread*
    ;; closing the socket usually drops accept via socket-error, but kill
    ;; the thread too just in case it's still alive
    (when (sb-thread:thread-alive-p *accept-thread*)
      (ignore-errors (sb-thread:terminate-thread *accept-thread*)))
    (setf *accept-thread* nil)
    (format t "namdel server stopped.~%")))

(defun accept-loop (socket)
  (handler-case
      (loop
        (let ((client (sb-bsd-sockets:socket-accept socket)))
          (sb-thread:make-thread
           (lambda ()
             (unwind-protect
                  (let ((stream (sb-bsd-sockets:socket-make-stream
                                 client :input t :output t
                                 :element-type '(unsigned-byte 8))))
                    (unwind-protect (handle-request stream) (close stream)))
               (sb-bsd-sockets:socket-close client)))
           :name "namdel-client")))
    (sb-bsd-sockets:socket-error ()
      (format t "namdel server: accept loop stopped.~%"))))

(defun start (&optional (port 4433))
  (stop)
  (let ((socket (make-instance 'sb-bsd-sockets:inet-socket :type :stream :protocol :tcp)))
    (setf (sb-bsd-sockets:sockopt-reuse-address socket) t)
    (handler-case
        ;; 0.0.0.0, not 127.0.0.1 -- otherwise unreachable from outside
        (sb-bsd-sockets:socket-bind socket #(0 0 0 0) port)
      (sb-bsd-sockets:socket-error (e)
        (ignore-errors (sb-bsd-sockets:socket-close socket))
        (error "Couldn't bind port ~a (~a)." port e)))
    (setf *server-socket* socket)
    (sb-bsd-sockets:socket-listen socket 16)
    (format t "namdel server started on 0.0.0.0:~a~%" port)
    (setf *accept-thread*
          (sb-thread:make-thread (lambda () (accept-loop socket))
                                 :name "namdel-accept"))
    (values)))

;; Auto-(re)start: reloading the file (C-c C-k in Portacle) re-runs it
;; top to bottom, so start calls stop first and comes back up fresh.
;; load-all-rooms! is a no-op on reload (guards on *rooms* being empty).
(load-all-rooms!)
(start)

(defvar *swank-started* nil)
(unless *swank-started*
  (load "/root/quicklisp/setup.lisp")
  (ql:quickload :swank)
  (swank:create-server :port 4005 :dont-close t :style :spawn)
  (setf *swank-started* t))

(defun list-rooms ()
  "Печатает все активные комнаты: ключ, hex-директорию и число pending."
  (maphash (lambda (key room)
             (format t "~a -> ~a: ~a pending~%"
                     key (room-dir key) (length (nam-room-pending room))))
           *rooms*))

(defun delete-room! (nickname birthdate)
  "Полностью удаляет комнату: из памяти (*rooms*) и с диска (~/rooms/<hex>/)."
  (let* ((key (room-key nickname birthdate))
         (dir (room-dir key)))
    (sb-thread:with-mutex (*rooms-lock*)
      (remhash key *rooms*))
    (uiop:run-program (list "rm" "-rf" dir) :ignore-error-status t)
    (format t "deleted room ~a -> ~a~%" key dir)))

