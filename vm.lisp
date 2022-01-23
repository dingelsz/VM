;; -----------------------------------------------------------------------------
;; Utils - General
;; -----------------------------------------------------------------------------
(defun nif (predicate)
  "An if statement that returns 1 for true and 0 for false (number-if)"
  (if predicate 1 0))

;; -----------------------------------------------------------------------------
;; Utils - Binary
;; We represent binary from left to right
;; -----------------------------------------------------------------------------
(defun bin-ref (bits n)
  "Returns the nth bit from a binary number"
  (nth n bits))

(defun bin-seq (bits start end)
  "Returns subsequence binary digets starting at digit start and ending at digit end"
  (subseq bits start end))

(defun bin-add (x y &optional (carry 0))
  "Adds two binary numbers together"
  ;; Two empty numbers
  (cond ((and (null x) (null y)) (list carry))
	((null x) y)
	((null y) x)
	(T (cons (mod (+ (first x) (first y) carry) 2)
		 (bin-add (rest x) (rest y) (nif (>= (+ (first x) (first y) carry) 2)))))))

(defun bin-to-int (bit)
  "Convert a binary number to an integer"
  (if (null bit) 0
      (+ (first bit) (* 2 (bin-to-int (rest bit))))))

(defun int-to-bin (num)
  "Converts an integer to a binary number"
  (if (zerop num) '()
      (cons (mod num 2) (num-to-bit (floor num 2)))))

(defun bin= (x y)
  (= (bin-to-int x) (bin-to-int y)))

(defun bin-zerop (num)
  (zerop (bin-to-int num)))
(defun bin-and (x y)
  (cond ((and (null x) (null y)) '())
	((null x) y)
	((null y) x)
	(T (cons (mod (+ (first x) (first y)) 2) (bin-and (rest x) (rest y))))))



;; -----------------------------------------------------------------------------
;; Utils - Read/Write
;; -----------------------------------------------------------------------------
(defun vm-read (sequence index)
  "Reads a value from the sequence at a given index"
  (gethash index sequence))

(defun vm-write (sequence index value)
  "Writes a value into the sequence at a given index"
  (setf (gethash index sequence) value))

;; -----------------------------------------------------------------------------
;; Memory
;; -----------------------------------------------------------------------------
(defparameter *WORD-SIZE* 16)
(defparameter *WORD* (loop repeat *WORD-SIZE* collect 0))
(defparameter *WORD-COUNT* (expt 2 16))
(defparameter *MEMORY* (loop
			 repeat *WORD-COUNT*
			 collect *WORD*))

(defun make-word () (loop repeat *WORD-SIZE* collect 0))

(defun memory-read (index)
  "Reads a value from memory at the given index"
  (vm-read *MEMORY* index))

(defun memory-write (index value)
  "Writes a value into memory at the given index"
  (vm-write *MEMORY* index value))

;; -----------------------------------------------------------------------------
;; Registers
;; -----------------------------------------------------------------------------
(defparameter REGISTERS (make-hash-table))
(setf (gethash 'R0 REGISTERS) *WORD*)
(setf (gethash 'R1 REGISTERS) *WORD*)
(setf (gethash 'R2 REGISTERS) *WORD*)
(setf (gethash 'R3 REGISTERS) *WORD*)
(setf (gethash 'R4 REGISTERS) *WORD*)
(setf (gethash 'R5 REGISTERS) *WORD*)
(setf (gethash 'R6 REGISTERS) *WORD*)
(setf (gethash 'R7 REGISTERS) *WORD*)
(setf (gethash 'RPC REGISTERS) *WORD*)
(setf (gethash 'RCND REGISTERS) *WORD*)
(setf (gethash 'RCNT REGISTERS) *WORD*)

(defun register-lookup (key)
  (if (symbolp key) key
      (cond ((bin= key (int-to-bin 0)) 'R0)
	    ((bin= key (int-to-bin 1)) 'R1)
	    ((bin= key (int-to-bin 2)) 'R2)
	    ((bin= key (int-to-bin 3)) 'R3)
	    ((bin= key (int-to-bin 4)) 'R5)
	    ((bin= key (int-to-bin 5)) 'R6)
	    ((bin= key (int-to-bin 6)) 'R7)
	    ((bin= key (int-to-bin 7)) 'RPC)
	    ((bin= key (int-to-bin 8)) 'RCND)
	    ((bin= key (int-to-bin 9)) 'RCNT))))

(defun register-read (R)
  (vm-read REGISTERS (register-lookup R)))

(defun register-write (R value)
  (vm-write REGISTERS (register-lookup R) value))

(defun register-inc (R value)
  (register-write (register-lookup R) (bin-add (register-read (register-lookup R))
					 value)))

(defun update-conditional-register (x)
  (register-write 'RCND (cond
			  ((< x 0) '(0 0 1))
			  ((= x 0) '(0 1 0))
			  ((> x 0) '(1 0 0)))))

;; -----------------------------------------------------------------------------
;; Instructions
;; ---------------------------------------------------------------------------
;; Memory Layout: (16 bits)
;; 0-4		: Op Code
;; 4-7		: Param 1
;; 7-10		: Param 2
;; 11		: Space
;; 12-16	: Param 3
;; ---------------------------------------------------------------------------

;; -----------------------------------------------------------------------------
;; Instructions - Implementation - Control Flow
;; ---------------------------------------------------------------------------
(defun op-branch (instruction)
  (let* ((offset (bin-seq instruction 0 9))
	(flags (bin-seq instruction 9 11))
	(should-branch (bin= '(0 0 0) (bin-and flags (register-read 'RCND)))))
    (when should-branch (register-inc 'RPC offset))))

(defun op-jump (instruction)
  (let* ((arg2 (bin-seq instruction 6 9))
	 (base (register-read 'RPC))
	 (address (register-read arg2)))
      (register-write 'RPC address)))

(defun op-jump-to-subroutine (instruction)
  (register-write 'R7 (register-read 'RPC))
  (let ((misc (bin-ref instruction 11))
	(offset (bin-seq instruction 0 10))
	(arg2 (bin-seq instruction 6 9)))
    (register-write 'RPC (if (zerop misc)
			     (register-read arg2)
			     (+ (register-read 'RPC) offset)))))

;; ---------------------------------------------------------------------------
;; Instructions - Implementation - Math
;; ---------------------------------------------------------------------------
(defun op-add (instruction)
  ;; Store the sum of two numbers in register (arg1). The sum is either
  ;; two numbers in registers (arg2 and arg3) or the sum of whats in
  ;; register (arg2) and the number arg3.
  (let ((arg1 (bin-seq instruction 9 12))
	(arg2 (bin-seq instruction 6 9))
	(misc (bin-seq instruction 3 6))
	(arg3 (bin-seq instruction 0 3)))
    (register-write arg1
		    (bin-add (register-read arg2)
		       (if (bin-zerop misc)
			   (register-read arg3)
			   arg3)))
;;    (update-conditional-register (register-read arg1))
    ))

(defun op-and (instruction)
  (let ((arg1 (bin-seq instruction 9 12))
	(arg2 (bin-seq instruction 6 9))
	(arg3 (bin-seq instruction 0 5))
	(misc (bin-ref instruction 5)))
    (register-write arg1
		    (bin-and (register-read arg2)
			     (if (zerop misc)
				 (register-read arg3)
				 arg3)))
    (update-conditional-register (register-read arg1))))

(defun op-not (instruction)
  (let ((arg1 (bin-seq instruction 9 12))
	(arg2 (bin-seq instruction 6 9)))
    (register-write arg1 (bit-not arg2))
    (update-conditional-register (register-read (arg1 insruction)))))

;; ---------------------------------------------------------------------------
;; Instructions - Implementation - Memory -> Registers
;; ---------------------------------------------------------------------------
(defun op-load (instruction)
  (let* ((base (register-read 'RPC))
	 (arg1 (bin-seq instruction 9 12))
	 (offset (bin-seq (binary instruction) 0 9))
	 (address (+ base offset)))
    (register-write arg1 (memory-read address))
    (update-conditional-register (register-read arg1))))

(defun op-load-base (instruction)
  (let* ((arg1 (bin-seq instruction 9 12))
	 (arg2 (bin-seq instruction 6 9))
	 (base (register-read arg2))
	 (offset (bin-seq (binary instruction) 0 6))
	 (address (+ base offset)))
    (register-write arg1 (memory-read address))
    (update-conditional-register (register-read arg1))))

(defun op-load-indirect (instruction)
  (let* ((arg1 (bin-seq instruction 9 12))
	 (base (register-read 'RPC))
	 (offset (bin-seq (binary instruction) 0 9))
	 (address (memory-read (+ base offset))))
    (register-write arg1 (memory-read address))
    (update-conditional-register (register-read arg1))))

(defun op-load-effective-address (instruction)
  (let* ((arg1 (bin-seq instruction 9 12))
	 (base (register-read 'RPC))
	 (offset (bin-seq (binary instruction) 0 9))
	 (address (+ base (memory-read offset))))
    (register-write arg1 address)
    (update-conditional-register (register-read arg1))))

;; ---------------------------------------------------------------------------
;; Instructions - Implementation - Registers -> Memory
;; ---------------------------------------------------------------------------
(defun op-store (instruction)
  (let* ((arg1 (bin-seq instruction 9 12))
	 (base (register-read 'RPC))
	 (offset (bin-seq (binary instruction) 0 9))
	 (address (+ base offset))
	 (val (register-read arg1)))
    (memory-write address (register-read val))))

(defun op-store-base (instruction)
  (let* ((arg1 (bin-seq instruction 9 12))
	 (arg2 (bin-seq instruction 6 9))
	 (base (register-read arg2))
	 (offset (bin-seq (binary instruction) 0 6))
	 (address (memory-read (+ base offset)))
	 (val (register-read arg1)))
    (memory-write address (register-read val))))

(defun op-store-indirect (instruction)
  (let* ((arg1 (bin-seq instruction 9 12))
	 (base (register-read 'RPC))
	 (offset (bin-seq (binary instruction) 0 9))
	 (address (memory-read (+ base offset)))
	 (val (register-read arg1)))
    (memory-write address (register-read val))))

;; -----------------------------------------------------------------------------
;; Instructions - Implementations - Traps
;; -----------------------------------------------------------------------------
(defun trap-input-character ()
  (register-write 'R0 (char-int (read-char))))

(defun trap-output-character ()
  (format T "~A" (register-read 'R0)))

(defun trap-output-string ()
  
  )

(defun trap-input-output-character ()
  (trap-input-character)
  (trap-output-character))

(defun trap-putsp ()
  
  )

(defun trap-halt ()
  (setf VM-RUNNING nil))

(defun trap-input-integer ()
  (register-write 'R0 (parse-integer (read-line))))

(defun trap-output-integer ()
  (format T "~D" (register-read 'R0)))

(defparameter TRAP-TABLE (make-hash-table))
(setf (gethash #x0 TRAP-TABLE) trap-input-character)
(setf (gethash #x1 TRAP-TABLE) trap-output-character)
(setf (gethash #x2 TRAP-TABLE) trap-output-string)
(setf (gethash #x3 TRAP-TABLE) trap-input-output-character)
(setf (gethash #x4 TRAP-TABLE) trap-putsp)
(setf (gethash #x5 TRAP-TABLE) trap-halt)
(setf (gethash #x6 TRAP-TABLE) trap-input-integer)
(setf (gethash #x7 TRAP-TABLE) trap-output-integer)

(defun op-trap (instruction)
  (let ((trap-idx (bin-seq instruction 0 8)))
    (funcall (gethash trap-idx TRAP-TABLE))))

(defun op-return-from-interrupt (instruction))


;; -----------------------------------------------------------------------------
;; Instructions - Op Table
;; ---------------------------------------------------------------------------
(defparameter OP-TABLE (make-hash-table))
(setf (gethash #x0 OP-TABLE) #'op-branch)
(setf (gethash #x1 OP-TABLE) #'op-add)
(setf (gethash #x2 OP-TABLE) #'op-load)
(setf (gethash #x3 OP-TABLE) #'op-store)
(setf (gethash #x4 OP-TABLE) #'op-jump-to-subroutine)
(setf (gethash #x5 OP-TABLE) #'op-and)
(setf (gethash #x6 OP-TABLE) #'op-load-base)
(setf (gethash #x7 OP-TABLE) #'op-store-base)
(setf (gethash #x8 OP-TABLE) #'op-return-from-interrupt)
(setf (gethash #x9 OP-TABLE) #'op-not)
(setf (gethash #xA OP-TABLE) #'op-load-indirect)
(setf (gethash #xB OP-TABLE) #'op-store-indirect)
(setf (gethash #xC OP-TABLE) #'op-jump)
(setf (gethash #xD OP-TABLE) NIL)
(setf (gethash #xE OP-TABLE) #'op-load-effective-address)
(setf (gethash #xF OP-TABLE) #'op-trap)


;; -----------------------------------------------------------------------------
;; Main
;; -----------------------------------------------------------------------------
(defparameter VM-RUNNING T)
(defparameter VM-PC-START #x3000)

(defun VM-run-step ()
  (when VM-RUNNING
    (let* ((instruction (register-read 'RPC))
	   (op (gethash (opcode instruction) OP-TABLE)))
      (funcall op instruction)
      (register-inc 'RPC 1)
      (VM-run-step))))

(defun VM-run (offset)
  (register-write 'RPC (+ VM-PC-START offset))
  (VM-run-step))

(defun VM-load (filename))

