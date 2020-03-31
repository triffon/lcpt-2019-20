(define (repeated n f x)
  (if (= n 0) x
      (f (repeated (- n 1) f x))))

(define (c n)
  (lambda (f)
    (lambda (x)
      (repeated n f x))))

(define c0 (c 0))
(define c1 (c 1))

;; (lambda (f x)  ...) ≠ (lambda (f) (lambda (x) ...))
;; (f x y) ≠ ((f x) y)

(define (1+ x) (+ x 1))

(define (printn c)
  ((c 1+) 0))

(define cs
  (lambda (n)
    (lambda (f)
      (lambda (x)
        (f ((n f) x))))))

(define c+
  (lambda (m)
    (lambda (n)
      (lambda (f)
        (lambda (x)
          ((m f) ((n f) x)))))))

(define c++
  (lambda (m) (m cs)))

(define (compose f g)
  (lambda (x)
    (f (g x))))

(define c*
  (lambda (m)
    (lambda (n)
      (lambda (f)
        (m (n f))))))

(define c*
  (lambda (m) (lambda (n) (compose m n))))

(define c**
  (lambda (m)
    (lambda (n)
      ((m (c+ n)) c0))))

(define cexp
  (lambda (m)
    (lambda (n)
      ((n (c* m)) c1))))

(define cexp*
  (lambda (m)
    (lambda (n)
      (n m))))

(define ctrue  (lambda (x) (lambda (y) x)))
(define cfalse (lambda (x) (lambda (y) y)))

(define (printb b)
  ((b #t) #f))

(define cnot
  (lambda (p)
    ((p cfalse) ctrue)))

(define cor
  (lambda (p) (p ctrue)))

(define cand
  (lambda (p)
    (lambda (q)
      ((p q) cfalse))))

(define c/2
  (lambda (n)
    ((n cnot) ctrue)))

;; (Succ (Succ (Succ Zero)))

(define constr-zero 'Zero)
(define constr-succ (lambda (x) (list 'Succ x)))

(define ccons
  (lambda (x)
    (lambda (y)
      (lambda (z)
        ((z x) y)))))

(define ccar
  (lambda (p) (p ctrue)))

(define ccdr
  (lambda (p) (p cfalse)))

(define (printpn p)
  (p (lambda (x)
       (lambda (y)
         (cons (printn x) (printn y))))))

(define cp
  (lambda (n)
    (ccdr
     ((n
       (lambda (p)
         ((ccons
           (cs (ccar p)))
          (ccar p))))
      ((ccons c0) c0)))))

(define c!
  (lambda (n)
    (ccdr
     ((n
       (lambda (p)
         ((ccons
           (cs (ccar p)))
          ((c* (cs (ccar p)))
           (ccdr p)))))
      ((ccons c0) c1)))))

