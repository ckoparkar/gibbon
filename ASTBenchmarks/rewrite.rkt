#lang racket

; (require racket/exn) ;; Not in Racket 6.2

(define (datum e)
  (if (fixnum? e)
      `(INTLIT ,e)
      '(INTLIT 5)))

(define (sym s)
  (define str (list->string (filter legit-char? (string->list (symbol->string s)))))
  (define str2
    (cond
      [(zero? (string-length str))
       "symbol-wiped-out-by-character-filtration"]
      [(not (ascii-alphabetic? (string-ref str 0)))
       (string-append "sym_" str)]
      [else str]))
  (string->symbol str2))

(define (legit-char? c)
  (or (ascii-alphabetic? c)
      (ascii-digit? c)
      (eq? c #\-)
      (eq? c #\_)
      ))

(define (ascii-alphabetic? c)
  (define n (char->integer c))
  (or (<= 65 n 90)  ;; A-Z
      (<= 97 n 122) ;; a-z
      ))

(define (ascii-digit? c)
  (define n (char->integer c))
  (<= 48 n 57))

  

(define (xform-expression e)
  (define xf xform-expression)
  #;
  (when (pair? e)
    (newline)
    (print (car e))
    (newline))

  (match e
    [`(if ,e1 ,e2 ,e3)          `(If ,(xf e1) ,(xf e2) ,(xf e3))]
    [`(set! ,x ,e)              `(SetBang ,(sym x) ,(xf e))]
    [`(quote ,e)                `(Quote            ,(datum e))]
    [`(quote-syntax ,e)         `(QuoteSyntax      ,(datum e))]
    [`(quote-syntax ,e #:local) `(QuoteSyntaxLocal ,(datum e))]
    [`(module ,m ,lang ,e ...)  `(Begin ,(mkexprlist (map xf e)))]
    [`(module* ,m ,lang ,e ...) `(Begin ,(mkexprlist (map xf e)))]
    [`(#%top . ,s) #:when (symbol? s) `(Top ,(sym s))] ;; RRN: fixed
    [`(begin ,e ...)            `(Begin ,(mkexprlist (map xf e)))]
    [`(begin0 ,e0 ,e ...)       `(Begin0 ,(xf e0) ,(mkexprlist (map xf e)))]
    [`(#%variable-reference)    `(VariableReferenceNull)]
    [`(#%variable-reference (#%top . ,i)) #:when (symbol? i) `(VariableReferenceTop ,(sym i))]
    [`(#%variable-reference ,i)           #:when (symbol? i) `(VariableReference ,(sym i))]
    [`(#%app ,rat ,e ...)            `(App ,(xf rat) ,(mkexprlist (map xf e)))]
    [`(#%plain-app ,rat ,e ...)      `(App ,(xf rat) ,(mkexprlist (map xf e)))]
    [`(let-values (,binds ...) ,body ...)
     `(LetValues ,(lvbind binds) ,(mkexprlist (map xf body)))]
    [`(letrec-values (,binds ...) ,body ...)
     `(LetrecValues ,(lvbind binds) ,(mkexprlist (map xf body)))] ;; RRN: fixed.
    [(? symbol? s) `(VARREF ,(sym s))]
    [`(lambda ,fmls ,body ...)
     `(Lambda ,(xform-fmls fmls) ,(mkexprlist (map xf body)))]
    [`(#%plain-lambda ,fmls ,body ...)
     `(Lambda ,(xform-fmls fmls) ,(mkexprlist (map xf body)))]
    [`(#%expression ,e) (xf e)]
    [`(case-lambda ,cl ...)
     `(CaseLambda ,(mklambdacaselist
                    (for/list ([c (in-list cl)])
                     `(MKLAMBDACASE ,(xform-fmls (first c))
                                    ,(map xf (rest c))))))]
    [`(with-continuation-mark ,e1 ,e2 ,e3)
     `(WithContinuationMark ,(xf e1) ,(xf e2) ,(xf e3))]
    ; [(? symbol? s) `(VARREF ,s)]
    ))

(define (lvbind l)
  (match l
    ['() '(NULLLVBIND)]
    [`(((,x ...) ,e) . ,rest) #:when (andmap symbol? x)
     `(CONSLVBIND ,(mksymlist (map sym x)) ,(xform-expression e)
                  ,(lvbind rest))]))

(define (xform-fmls a)
  (match a
    [`(,fmls ...) `(F1 ,(mksymlist (map sym fmls)))]
    [`(,fmls ... . ,(? symbol? x))
     `(F2 ,(mksymlist (map sym fmls)) ,(sym x))]
    [(? symbol? x)
     `(F3 ,(sym x))]))

(define (mktoplist ls)
  (if (null? ls)
      '(NULLTOPLVL)
      `(CONSTOPLVL ,(car ls) ,(mktoplist (cdr ls)))))

(define (mkexprlist ls)
  (if (null? ls)
      '(NULLEXPR)
      `(CONSEXPR ,(car ls) ,(mkexprlist (cdr ls)))))

(define (mksymlist ls)
  (if (null? ls)
      '(NULLSYM)
      `(CONSSYM ,(car ls) ,(mksymlist (cdr ls)))))

(define (mklambdacaselist l)
  (match l
    ['() `(NULLLAMBDACASE)]
    [`((MKLAMBDACASE ,a ,b) . ,rest)
     `(CONSLAMBDACASE ,a ,(mkexprlist b) ,(mklambdacaselist rest))]))


(define (xform-top e)
  (match e
    [(? eof-object?) #f]  ;; empty file
    [`(#%require ,_ ...) `(BeginTop (NULLTOPLVL))]
    [`(#%provide ,_ ...) `(BeginTop (NULLTOPLVL))]
    [`(#%declare ,_ ...) `(BeginTop (NULLTOPLVL))] ;; RRN added.
    [`(module ,m ,lang ,e ...)  `(BeginTop ,(mktoplist (map xform-top e)))]
    [`(module* ,m ,lang ,e ...) `(BeginTop ,(mktoplist (map xform-top e)))]
    [`(begin ,e ...)
     `(BeginTop ,(mktoplist (map xform-top e)))]
    [`(begin-for-syntax ,e ...)  ;; RRN added.
     `(BeginTop ,(mktoplist (map xform-top e)))]
    [`(#%module-begin ,e ...)
     `(BeginTop ,(mktoplist (map xform-top e)))]
    [`(#%plain-module-begin ,e ...)
     `(BeginTop ,(mktoplist (map xform-top e)))]
    [`(define-values (,x ...) ,e)
     `(DefineValues ,(mksymlist (map sym x)) ,(xform-expression e))]
    [`(define-syntaxes (,x ...) ,e)
     `(DefineSyntaxes ,(mksymlist (map sym x)) ,(xform-expression e))]
    [e `(Expression ,(xform-expression e))]))

;; ----------------------------------------

;; expects "<infile> <outfile>" lines on stdin
;; runs until it gets no more such lines (EOF)
(module+ main
  (let ([errors 0])
    (let loop ()
      (define l (read-line))
      (if (eof-object? l)
          (printf "rewrite.rkt: Reached EOF; done.\n")
          (match (string-split l)
            [(list infile outfile)
             (printf "Converting: ~a ~a\n" infile outfile)
             (with-handlers ([(lambda (_) #t)
                              (lambda (e)
                                (printf "ERROR while converting:\n  ~a"
                                        ; (exn->string e) ;; Not in Racket 6.2
                                        e)
                                (set! errors (add1 errors)))])
               (let* ((v (with-input-from-file infile read))
                      (new                   
                       (xform-top v)))
                 (when new
                   (with-output-to-file outfile
                     (lambda () (write new) (newline))))))
             (loop)]
            )))
    (if (zero? errors)
        (printf "Completed all conversions without error.\n")
        (begin (printf "Encountered ~a errors while converting.  Failing job.\n" errors)
               (exit 1)))
    ))
