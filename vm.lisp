;; -----------------------------------------------------------------------------
;; Utils - Binary
;; -----------------------------------------------------------------------------
(defun bit-ref (binary nth)
  "Returns the nth bit from a binary number"
  )

(defun bit-right (number offset)
  "Returns offset binary digets from the right of the number")

(defun bit-left (number offset)
  "Returns offset binary digets from the left of the number")

(defun bit-seq (number start end)
  "Returns subsequence binary digets starting at digit start and ending at digit end")

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
(defparameter MEMORY (make-hash-table))

(defun memory-read (index)
  "Reads a value from memory at the given index"
  (vm-read MEMORY index))

(defun memory-write (index value)
  "Writes a value into memory at the given index"
  (vm-write MEMORY index value))

;; -----------------------------------------------------------------------------
;; Registers
;; -----------------------------------------------------------------------------
(defparameter REGISTERS (make-hash-table))
(setf (gethash 'R0 REGISTERS) 0)
(setf (gethash 'R1 REGISTERS) 0)
(setf (gethash 'R2 REGISTERS) 0)
(setf (gethash 'R3 REGISTERS) 0)
(setf (gethash 'R4 REGISTERS) 0)
(setf (gethash 'R5 REGISTERS) 0)
(setf (gethash 'R6 REGISTERS) 0)
(setf (gethash 'R7 REGISTERS) 0)
(setf (gethash 'RPC REGISTERS) 0)
(setf (gethash 'RCND REGISTERS) 0)
(setf (gethash 'RCNT REGISTERS) 0)


(defun register-read (R)
  (vm-read REGISTERS R))

(defun register-write (R value)
  (vm-write REGISTERS R value))

(defun register-inc (R value)
  (register-write R (+ (register-read R)
		       value)))

(defun update-conditional-register (x)
  (register-write 'RCND (cond
			  ((< x 0) #b001)
			  ((= x 0) #b010)
			  ((> x 0) #b100))))

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
(defstruct instruction "An instruction"
	   (binary 0)
	   (op 0)
	   (arg1 0)
	   (arg2 0)
	   (misc 0)
	   (param3 0))

(defun make-instruction-from-int (x)
  "Makes a new instruction from an integer"
  (let ((opcode (bit-seq 0 4))
	(arg1   (bit-seq 4 7))
	(arg2   (bit-seq 7 10))
	(misc   (bit-ref 11))
	(param3 (bit-sub 12 16)))
    (make-instruction :binary x :opcode opcode :param1 arg1 :param2 arg2 :misc misc :param3 param3)))

;; -----------------------------------------------------------------------------
;; Instructions - Implementation
;; ---------------------------------------------------------------------------
;; - Control Flow
;; ---------------------------------------------------------------------------
(defun op-branch (instruction)
  (let* ((offset (bit-seq instruction 0 9))
	(flags (bit-seq instruction 9 11))
	(should-branch (= #x000 (bit-and flags (register-read 'RCND)))))
    (when should-branch (register-inc 'RPC offset))))

(defun op-jump (instruction)
    (let* ((register (arg2 instruction))
	 (base (register-read 'RPC))
	 (address (register-read register)))
      (register-write 'RPC address)))

(defun op-jump-to-subroutine (instruction)
  (register-write 'R7 (register-read 'RPC))
  (let ((offset (bit-seq instruction 0 10)))
    (register-write 'RPC (if (zerop (bit-ref instruction 11))
			     (register-read (arg2 instruction))
			     (+ (register-read 'RPC) offset)))))

;; ---------------------------------------------------------------------------
;; Instructions - Implementation - Math
;; ---------------------------------------------------------------------------
(defun op-add (instruction)
  ;; Store the sum of two numbers in register (arg1). The sum is either
  ;; two numbers in registers (arg2 and arg3) or the sum of whats in
  ;; register (arg2) and the number arg3.
  (register-write (arg1 instruction)
		  (+ (register-read (arg2 instruction))
		     (if (zerop (misc instruction))
			 (register-read (arg3 instruction))
			 (arg3 instruction))))
  (update-conditional-register (register-read (arg1 insruction))))

(defun op-and (instruction)
  (register-write (arg1 instruction)
		  (bit-and (register-read (arg2 instruction))
			   (if (zerop (misc instruction))
			       (register-read (arg3 instruction))
			       (arg3 instruction))))
  (update-conditional-register (register-read (arg1 insruction))))

(defun op-not (instruction)
  (register-write (arg1 instruction) (bit-not (arg2 instruction)))
  (update-conditional-register (register-read (arg1 insruction))))

;; ---------------------------------------------------------------------------
;; Instructions - Implementation - Memory -> Registers
;; ---------------------------------------------------------------------------
(defun op-load (instruction)
  (let* ((base (register-read 'RPC))
	 (offset (bit-right (binary instruction) 9))
	 (address (+ base offset)))
    (register-write (arg1 instruction) (memory-read address)))
  (update-conditional-register (register-read (arg1 insruction))))

(defun op-load-base (instruction)
  (let* ((base (register-read (arg2 instruction)))
	 (offset (bit-right (binary instruction) 6))
	 (address (+ base offset)))
    (register-write (arg1 instruction) (memory-read address)))
  (update-conditional-register (register-read (arg1 insruction))))

(defun op-load-indirect (instruction)
  (let* ((base (register-read 'RPC))
	 (offset (bit-right (binary instruction) 9))
	 (address (memory-read (+ base offset))))
    (register-write (arg1 instruction) (memory-read address)))
  (update-conditional-register (register-read (arg1 insruction))))

(defun op-load-effective-address (instruction)
  (let* ((base (register-read 'RPC))
	 (offset (bit-right (binary instruction) 9))
	 (address (+ base (memory-read offset))))
    (register-write (arg1 instruction) address))
  (update-conditional-register (register-read (arg1 insruction))))

;; ---------------------------------------------------------------------------
;; Instructions - Implementation - Registers -> Memory
;; ---------------------------------------------------------------------------
(defun op-store (instruction)
  (let* ((base (register-read 'RPC))
	 (offset (bit-right (binary instruction) 9))
	 (address (+ base offset))
	 (val (register-read (arg1 instruction))))
    (memory-write address (register-read val))))

(defun op-store-base (instruction)
  (let* ((base (register-read (arg2 instruction)))
	 (offset (bit-right (binary instruction) 6))
	 (address (memory-read (+ base offset)))
	 (val (register-read (arg1 instruction))))
    (memory-write address (register-read val))))

(defun op-store-indirect (instruction)
  (let* ((base (register-read 'RPC))
	 (offset (bit-right (binary instruction) 9))
	 (address (memory-read (+ base offset)))
	 (val (register-read (arg1 instruction))))
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
  (let ((trap-idx (bit-seq instruction 0 8)))
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

