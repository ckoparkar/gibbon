#lang typed/racket/base

(require racket/system
	 racket/match
	 racket/string)

(provide driver)

(define target-time 1.0)
(define ARGMAX 25)

;; CSV
;; NAME, VARIANT, ARGS, ITERS, MEANTIME

;; `read-line`, `split-string`, `(match _ [(list "BATCHTIME:" t) …` right?
;; reads until it finds BATCHTIME
(define (read-batchtime [port : Input-Port]) : Real	 
  (define line (read-line port 'any))
  (define strs (string-split (cast line String)))
  (match strs
    [`("BATCHTIME:" ,t)
    (cast (string->number t) Real)]
    [_ (read-batchtime port)]))

;; port that proccess wrote to
(define (get-input-port ls)
  (match ls
   [`(,ip ,op ,pid ,stde ,proc)
    ip]))

(define (driver [csv-port : Output-Port] [exec : String] [pass-name : String]
		[variant : String])
  (fprintf csv-port "NAME, VARIANT, ARGS, ITERS, MEANTIME\n") ;; start csv file
  
  ;; loop through args 1 to 25
  (for ([args (in-range 1 (+ 1 ARGMAX))])
    (let loop ([iters 1])
      (define ls (process (format "~a ~a ~a" exec args iters)))
      (define op (get-input-port ls))

      (define batchseconds (read-batchtime op))
      (if (>= batchseconds target-time)
          (let ([meantime (exact->inexact (/ batchseconds iters))])
	    (printf "\nITERS: ~a\n" iters)
            (printf "BATCHTIME: ~a\n" (exact->inexact batchseconds))
            (printf "MEANTIME: ~a\n" meantime)
            (printf "Done with pass, ~a.\n" pass-name)

	    ;; write to csv
	    (fprintf csv-port "~a, ~a, ~a, ~a, ~a\n"
	  	     pass-name variant args iters meantime)
	    (flush-output csv-port)
	    )
	  (begin (printf "~a " batchseconds) (flush-output)
	         (loop (* 2 iters)))))))