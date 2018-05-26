;; -*- geiser-scheme-implementation: racket -*-
#lang sicp

;; ----------------------------------

;; e1p1
;; skipped

;; ----------------------------------

;; e1p2
;; (/ (+ 5 4 (- 2 (- 3 (+ 6 (/ 4 5))))) (* 2 (- 6 2) (- 2 7)))


;; ----------------------------------

;; e1p3
;; (define (e1p3 a b c)
;;                 (cond ((and (<= a b) (<= a c)) (+ (* b b) (* c c)))
;;                       ((and (<= b a) (<= b c)) (+ (* a a) (* c c)))
;;                       (else (+ (* a a) (* b b)))))
;; (e1p3 1 2 3)

;; ----------------------------------

;; e1p4
;; return (a + b) if b > 0 otherwise (a - b)


;; ----------------------------------

;; e1p5
;; (define (p) (p))
;; (define (test x y)
;;    (if (= x 0)
;;        0
;;        y))
;; (test 0 (p))

;; (p) is infinitely recursive to itself. Running (p) would cause a non-stop loop.
;; interpret-or order interpreter will run (p).

;; ----------------------------------

;; e1p6
;; Both statements in the new-if body will run. So the program will not stop.

;; ----------------------------------

;; e1p7
;; When the number become larger, its square grows faster, so this program may require quite so time to stop.
;; When the number become closer to zero, its square become much smaller. The square of two numbers may be close enough, but their roots will not necessarily be so.
;; Just check the difference between each iteration.
;; (define (gut-genug? schaetzwert x)
;;   (< (abs (- (quadrat schaetzwert) x)) 0.0001))

;; ----------------------------------

;; e1p8
;; (define (verbessern2 y x)
;;   (/ (+ (/ x (* y y)) (* 2 y)) 3))
;; (define (gut-genug2? schaetzwert schaetzwert2)
;;   (< (abs (- schaetzwert schaetzwert2)) 0.0001))
;; (define  (kubikwurzel-iter schaetzwert x)
;;   (define schaetzwert2 (verbessern2 schaetzwert x))
;;   (if (gut-genug2? schaetzwert schaetzwert2)
;;       schaetzwert2
;;       (kubikwurzel-iter schaetzwert2 x)))
;; (kubikwurzel-iter 1.0 8.0)

;; ----------------------------------

;; e1p9
;; The first is recursive, and the second is iterative.

;; ----------------------------------

;; e1p10
;; (define (A x y)
;;   (cond ((= y 0) 0)
;;         ((= x 0) (* 2 y))
;;         ((= y 1) 2)
;;         (else (A (- x 1)
;;                  (A x (- y 1))))))
;; (define (f n) (A 0 n))
;; (define (g n) (A 1 n))
;; (define (h n) (A 2 n))
;; (define (k n) (* 5 n n))
;; (define seq '(1 2 3 4))
;; (map f seq)
;; (map g seq)
;; (map h seq)
;; (map h '(1 2 3))
;; (h 4)
;; By the computation above, one can guess f(n)=2n, g(n)=2^n. Let p(n)=n^2, then h(n)=p\circ \cdots \circ(2), where the composition is repeated (n-1) times.

;; ----------------------------------

;; e1p11
;; (define seq '(1 2 3 4))
;; (define (e1p11 n)
;;   (if (< n 3) n
;;       (+ (e1p11 (- n 1))
;;          (* 2 (e1p11 (- n 2)))
;;          (* 3 (e1p11 (- n 3))))))
;; (map e1p11 seq)
;; (define (e1p112 a b c counter)
;;   (if (= counter 0)
;;       c
;;       (e1p112 (+ a (* 2 b) (* 3 c)) a b (- counter 1))))
;; (define (recursive n)
;;   (e1p112 2 1 0 n)
;; )
;; (map recursive seq)


;; ----------------------------------

;; e1p12
;; (define (e1p12 n m)
;;   (if (or (= m 1) (= m n))
;;       1
;;       (+ (e1p12 (- n 1) (- m 1))
;;          (e1p12 (- n 1) m))))
;; (e1p12 6 2)

;; ----------------------------------

;; e1p13
;; This is a simple mathematical induction. Note that \phi and \psi are the roots of x^2 - x - 1 =0
;; As for the second proposition, note that Fib(n) is an integer, and \phi^n/\sqrt(5) < 1/2.

;; ----------------------------------

;; e1p14
;; TODO, skipped

;; ----------------------------------

;; e1p15
;; TODO, skipped

;; ----------------------------------

;; e1p16
;; (define (gerade? n)
;;   (= (remainder n 2) 0))
;; (define (e1p16 a b n)
;;   (if (= n 0)
;;       a
;;       (if (gerade? n)
;;           (e1p16 (* a b (/ n 2)) b (/ n 2))
;;           (e1p16 (* a b) b (- n 1)))))
;; (e1p16 1 2 4)

;; ----------------------------------

;; e1p17
;; (define (e1p17 a b n)
;;   (if (= n 0)
;;       a
;;       (if (gerade? n)
;;           (e1p17 (e1p17 a b (/ n 2)) b (/ n 2))
;;           (e1p17 (+ a b) b (- n 1)))))
;; (e1p17 0 4 6)

;; ----------------------------------

;; e1p18
;; (define (e1p18 a n)
;;   (if (= n 1)
;;       a
;;       (if (gerade? n)
;;           (+ (e1p18 a (/ n 2)) (e1p18 a (/ n 2)))
;;           (+ (e1p18 a (- n 1)) a))))
;; (e1p18 4 6)

;; ----------------------------------

;; e1p19
;; (define (fib-iter a b p q zaehler)
;;   (if (= zaehler 0)
;;       b
;;       (if (gerade? zaehler)
;;           (fib-iter a b
;;                     (+ (* q q) (* p p))
;;                     (+ (* q q) (* 2 p q))
;;                     (/ zaehler 2))
;;           (fib-iter (+ (* p a) (* q a) (* q b))
;;                     (+ (* q a) (* p b))
;;                     p q
;;                     (- zaehler 1)))))
;; (define (fib n)
;;   (fib-iter 1 0 0 1 n))
;; (define seq '(1 2 3 4))
;; (map fib seq)

;; ----------------------------------

;; e1p20
;; TODO, skipped

;; ----------------------------------

;; e1p21
;; (define (quadrat x)
;;   (* x x))
;; (define (teilt? a b)
;;   (= (remainder b a) 0))
;; (define (finde-teiler n pruef-teiler)
;;   (cond ((> (quadrat pruef-teiler) n) n)
;;         ((teilt? pruef-teiler n) pruef-teiler)
;;         (else (finde-teiler n (+ pruef-teiler 1)))))
;; (define (kleinster-teiler n)
;;   (finde-teiler n 2))
;; (define seq '(199 1999 19999))
;; (map kleinster-teiler seq)

;; ----------------------------------

;; e1p22
;; (define (quadrat x)
;;   (* x x))
;; (define (teilt? a b)
;;   (= (remainder b a) 0))
;; (define (finde-teiler n pruef-teiler)
;;   (cond ((> (quadrat pruef-teiler) n) n)
;;         ((teilt? pruef-teiler n) pruef-teiler)
;;         (else (finde-teiler n (+ pruef-teiler 1)))))
;; (define (kleinster-teiler n)
;;   (finde-teiler n 2))
;; (define (primzahl? n)
;;   (= (kleinster-teiler n) n))
;; (define (primzahl-test-zeit n)
;;   (newline)
;;   (display n)
;;   (start-primzahl-test n (runtime)))
;; (define (start-primzahl-test n startzeit)
;;   (if (primzahl? n)
;;       (ausgabe-laufzeit (- (runtime) startzeit))))
;; (define (ausgabe-laufzeit laufzeit)
;;   (display " *** ")
;;   (display laufzeit))
;; (define (smallest-prime n)
;;   (if (primzahl? n)
;;       n
;;       (smallest-prime (+ n 1))))
;; (define seq '(1000000 10000000 100000000))
;; (primzahl-test-zeit (smallest-prime 100000000000))

;; ----------------------------------

;; e1p23
;; (define (quadrat x)
;;   (* x x))
;; (define (teilt? a b)
;;   (= (remainder b a) 0))
;; (define (kleinster-teiler n)
;;   (finde-teiler n 2))
;; (define (primzahl? n)
;;   (= (kleinster-teiler n) n))
;; (define (primzahl-test-zeit n)
;;   (newline)
;;   (display n)
;;   (start-primzahl-test n (runtime)))
;; (define (start-primzahl-test n startzeit)
;;   (if (primzahl? n)
;;       (ausgabe-laufzeit (- (runtime) startzeit))))
;; (define (ausgabe-laufzeit laufzeit)
;;   (display " *** ")
;;   (display laufzeit))
;; (define (smallest-prime n)
;;   (if (primzahl? n)
;;       n
;;       (smallest-prime (+ n 1))))
;; (define (finde-teiler n pruef-teiler)
;;             (cond ((> (quadrat pruef-teiler) n) n)
;;                   ((teilt? pruef-teiler n) pruef-teiler)
;;                   (else (finde-teiler n (+ pruef-teiler 1)))))
;; (define (next n)
;;             (cond ((= n 2) 3)
;;                   (else (+ n 2))))
;; (define (finde-teiler n pruef-teiler)
;;             (cond ((> (quadrat pruef-teiler) n) n)
;;                   ((teilt? pruef-teiler n) pruef-teiler)
;;                   (else (finde-teiler n (next pruef-teiler)))))
;; (primzahl-test-zeit (smallest-prime 10000000000))

;; 18 error> (define (potmod basis exp m)
;;             (cond ((= exp 0) 1)
;;                   ((gerade? exp)
;;                    (remainder (quadrat (potmod basis (/ exp 2) m)) m) )
;;                   (else
;;                    (remainder (* basis (potmod basis (- exp 1) m))
;; m))) )

;; ----------------------------------

;; e1p25
;; (define (smallest-divisor n)
;;   (find-divisor n 2))

;; (define (smallest-divisor2 n)
;;   (find-divisor2 n 2))

;; (define (find-divisor n test-divisor)
;;   (cond ((> (square test-divisor) n) n)
;;         ((divides? test-divisor n) test-divisor)
;;         (else (find-divisor n (+ test-divisor 1)))))

;; (define (find-divisor2 n test-divisor)
;;   (define (next n)
;;     (cond ((= n 2) 3)
;;           (else (+ n 2))))
;;   (cond ((> (square test-divisor) n) n)
;;         ((divides? test-divisor n) test-divisor)
;;         (else (find-divisor n (next test-divisor)))))

;; (define (divides? a b)
;;   (= (remainder b a) 0))

;; (define (prime? n)
;;   (= n (smallest-divisor n)))

;; (define (prime?2 n)
;;   (= n (smallest-divisor2 n)))

;; (define (square n)
;;   (* n n))

;; (define (expmod base exp m)
;;   (cond ((= exp 0) 1)
;;         ((even? exp)
;;          (remainder
;;           (square (expmod base (/ exp 2) m))
;;           m))
;;         (else
;;          (remainder
;;           (* base (expmod base (- exp 1) m))
;;           m))))

;; (define (fermat-test n)
;;   (define (try-it a)
;;     (= (expmod a n n) a))
;;   (try-it (+ 1 (random (- n 1)))))

;; (define (fast-prime? n times)
;;   (cond ((= times 0) true)
;;         ((fermat-test n) (fast-prime? n (- times 1)))
;;         (else false)))

;; (define (prime?3 n)
;;   (fast-prime? n 100))

;; (define (least-prime algorithm n)
;;   (if (algorithm n)
;;       n
;;       (least-prime algorithm (+ n 1))))

;; (display (least-prime prime? 100000000))
;; (display "\n")
;; (display (least-prime prime?2 100000000))
;; (display "\n")
;; (display (least-prime prime?3 100000000))
;; (display "\n")

;; (define (timed-prime-test algorithm n)
;;   (newline)
;;   (display n)
;;   (start-prime-test n algorithm (runtime)))

;; (define (start-prime-test n algorithm start-time)
;;   (if (algorithm n)
;;       (report-prime (- (runtime) start-time))))

;; (define (report-prime elapsed-time)
;;   (display " *** ")
;;   (display elapsed-time))

;; (timed-prime-test prime? (least-prime prime?3  1000000000))
;; (timed-prime-test prime?2 (least-prime prime?3 1000000000))
;; (timed-prime-test prime?3 (least-prime prime?3 1000000000))

;; ----------------------------------

;; e1p26
;; (define (fermat-test-result n)
;;   (define (fermat-test-all n)
;;     (define (square n)
;;       (* n n))
;;     (define (expmod base exp m)
;;       (cond ((= exp 0) 1)
;;             ((even? exp)
;;              (remainder
;;               (square (expmod base (/ exp 2) m))
;;               m))
;;             (else
;;              (remainder
;;               (* base (expmod base (- exp 1) m))
;;               m))))
;;     (define (try-it a)
;;       (= (expmod a n n) a))
;;     (define a 1)
;;     (if (= a n)
;;         true
;;         (if (not (try-it a))
;;             false
;;             (try-it (+ a 1)))))
;;   (display n)
;;   (if (fermat-test-all n)
;;       (display " is a camichael number\n")
;;       (display " is not a camichael number\n")))

;; (map fermat-test-result '(561 1105 1729 2465 2821 6601 10000))

;; ----------------------------------

;; e1p27 
;; (define (e1p28 n)
;;   (define (square x)
;;     (* x x))  
;;   (Define (squaremod-with-check x)
;;     (let ((x_squared (square x)))
;;       (if (and (= x_squared 1)
;;                (not (= x (- n 1)))
;;                (not (= x 1)))
;;           0
;;           x_squared)))
;;   (define (expmod base exp m)
;;     (cond ((= exp 0) 1)
;;           ((even? exp)
;;            (squaremod-with-check (expmod base (/ exp 2) m)))
;;           (else
;;            (remainder
;;             (* base (expmod base (- exp 1) m))
;;             m))))
;;   (define (check a)
;;     (let ((result (expmod a (- n 1) n)))
;;       (if (or (not (= result 1)) (= result 0))
;;           true
;;           false)))
;;   (define (check-n-times n times)
;;     (if (= times 2)
;;         true
;;         (if (not (check (+ (random (- n 1)) 1)))
;;             false
;;             (check-n-times n (- times 1)))))
;;   (define (show-result)
;;     (display n)
;;     (if (check-n-times n 100)
;;         (display " is a prime\n")
;;         (display " is not a prime\n")))
;;   (show-result))

;; (map e1p28 '(561 1105 1729 2465 2821 6601 10000))

;; ----------------------------------

;; e1p30

;; (define (e1p30 term a naechstes b)
;;   (define (iter a ergebnis)
;;     (if (= a b)
;;         (+ ergebnis (term a))
;;         (iter (naechstes a) (+ ergebnis (term a)))))
;;   (iter a 0))

;; ----------------------------------

;; e1p31
;; (define (e1p31 a b)
;;   (define (prod term a naechstes b)
;;     (define (iter k ergebnis)
;;       (if (> k b)
;;           (* ergebnis 1)
;;           (iter (naechstes k) (* ergebnis (term k)))))
;;     (iter a 1))
;;   (define (term k)
;;     (if (= (remainder k 2) 0)
;;         (/ (+ 2.0 k) (+ 1.0 k))
;;         (/ (+ 1.0 k) (+ 2.0 k))))
;;   (define (naechstes k)
;;     (+ k 1))
;;   (* 4 (prod term a naechstes b)))
;; (e1p31 1 1000000)

;; (define (e1p31 a b)
;;   (define (prod term a naechstes b)
;;     (if (> a b)
;;         1
;;         (* (prod term (naechstes a) naechstes b) (term a))))
;;   (define (term k)
;;     (if (= (remainder k 2) 0)
;;         (/ (+ 2.0 k) (+ 1.0 k))
;;         (/ (+ 1.0 k) (+ 2.0 k))))
;;   (define (naechstes k)
;;     (+ k 1))
;;   (* 4 (prod term a naechstes b)))
;; (e1p31 1 1)

;; ----------------------------------

;; e1p32


;; (define (akkumulator kombinierer null-groesse term a naechstes b)
;;   (define (iter k ergebnis)
;;     (if (= a b)
;;         (kombinierer ergebnis (term b))
;;         (iter (naechstes k) (kombinierer (term k) ergebnis))))
;;   (iter a null-groesse))

;; (define (akkumulator kombinierer null-groesse term a naechstes b)
;;   (if (> a b)
;;       null-groesse
;;       (kombinierer (term a) (akkumulator kombinierer null-groesse term (naechstes a) naechstes b))))
;; (define (e1p31 a b)
;;   (define (prod term a naechstes b)
;;     (akkumulator * 1 term a naechstes b))
;;   (define (term k)
;;     (if (= (remainder k 2) 0)
;;         (/ (+ 2.0 k) (+ 1.0 k))
;;         (/ (+ 1.0 k) (+ 2.0 k))))
;;   (define (naechstes k)
;;     (+ k 1))
;;   (* 4 (prod term a naechstes b)))
;; (e1p31 1 100)

;; ----------------------------------

;; e1p33
;; (define (akkumulator kombinierer filter null-groesse term a naechstes b)
;;   (if (> a b)
;;       null-groesse
;;       (if (filter a)
;;           (akkumulator kombinierer filter null-groesse term (naechstes a) naechstes b)
;;           (kombinierer (term a) (akkumulator kombinierer filter null-groesse term (naechstes a) naechstes b)))))

;; (define (e1p33a a b)
;;   (define (not_prime? n)
;;     (define (square x)
;;       (* x x))  
;;     (define (find-divisor n test-divisor)
;;       (define (divides? a b)
;;         (= (remainder b a) 0))
;;       (define (next n)
;;         (cond ((= n 2) 3)
;;               (else (+ n 2))))
;;       (cond ((> (square test-divisor) n) n)
;;             ((divides? test-divisor n) test-divisor)
;;             (else (find-divisor n (next test-divisor)))))
;;     (define (smallest-divisor n)
;;       (find-divisor n 2))
;;     (or (not (= n (smallest-divisor n))) (= n 1)))
;;   (define (prime_sum term a naechstes b)
;;     (akkumulator + not_prime? 0 term a naechstes b))
;;   (define (term k)
;;     k)
;;   (define (naechstes k)
;;     (+ k 1))
;;   (prime_sum term a naechstes b))
;; (e1p33a 1 10)

;; (define (e1p33b n)
;;   (define (not_relatively_prime? x)
;;     (not (= (gcd x n) 1)))
;;   (define (relatively_prime_sum n)
;;     (akkumulator + not_relatively_prime? 0 (lambda (k) k) 0 (lambda (k) (+ k 1)) n))
;;   (relatively_prime_sum n))
;; (e1p33b 5)

;; ----------------------------------

;; e1p34
;; f takes functions as its argument, (f 2) = (2 2), 2 is not a function.
;; (define (f g)
;;   (g 2))
;; (f f )

;; ----------------------------------

;; e1p35
;; (define tolerence 0.00001)
;; (define (fixed-point f first-guess)
;;   (define (close-enough? v1 v2)
;;     (< (abs (- v1 v2)) tolerence))
;;   (define (try f guess)
;;     (let ((next (f guess)))
;;       (if (close-enough? next guess)
;;           next
;;           (try f next))))
;;   (try f first-guess))
;; (fixed-point (lambda (x) (+ 1 (/ 1 x))) 1.0)

;; ----------------------------------

;; e1p36
;; (define (fixed-point f first-guess)
;;   (define tolerance 0.00001)
;;   (define (close-enough? v1 v2)
;;     (< (abs (- v1 v2)) tolerance))
;;   (define (try guess)
;;     (display guess)
;;     (newline)
;;     (let ((next (f guess)))
;;       (if (close-enough? guess next)
;;           next
;;           (try next))))
;;   (try first-guess))

;; (define (fixed-point-with-average-damping f first-guess)
;;   (define tolerance 0.00001)
;;   (define (close-enough? v1 v2)
;;     (< (abs (- v1 v2)) tolerance))
;;   (define (try guess)
;;     (display guess)
;;     (newline)
;;     (let ((next (f guess)))
;;       (if (close-enough? guess next)
;;           next
;;           (try (/ (+ guess next) 2)))))
;;   (try first-guess))

;; (define (equation-to-solve x)
;;   (/ (log 1000) (log x)))

;; (fixed-point-with-average-damping equation-to-solve 2.0)
;; (fixed-point equation-to-solve 2.0)

;; ----------------------------------

;; e1p37
;; (define tolerence 0.00001)
;; (define (ketten-bruch2 D_i N_i tiefe)
;;   (define (wrapped-ketten-bruch D_i N_i tiefe)
;;     (let ((formal_result (ketten-bruch2 (lambda (i) (D_i (+ i 1))) (lambda (i) (N_i (+ i 1))) (- tiefe 1))))
;;       (define latter_result (/ (N_i 1)
;;                                (+ (D_i 1) formal_result)))
;;       (if (< (abs (- formal_result latter_result)) toleren)
;;           (display tiefe))
;;       latter_result))
 
;;   (if (= tiefe 1)
;;       (/ (N_i 1) (D_i 1))
;;       (wrapped-ketten-bruch D_i N_i tiefe)))

;; (define (ketten-bruch D_i N_i tiefe)
;;   (if (= tiefe 1)
;;       (/ (N_i 1) (D_i 1))
;;       (/ (N_i 1) (+ (D_i 1)
;;                     (ketten-bruch (lambda (i) (D_i (+ i 1))) (lambda (i) (N_i (+ i 1))) (- tiefe 1))))))

;; (define (phi tiefe)
;;   (/ 1 (ketten-bruch2 (lambda (i) 1.0)
;;                      (lambda (i) 1.0)
;;                      tiefe)))
;; (define (test tiefe)
;;   (ketten-bruch (lambda (i) 1)
;;                 (lambda (i) i)
;;                 tiefe))
;; (phi 100)

;; (define (ketten-bruch-iter D_i N_i tiefe)
;;   (define (iter D_i N_i tiefe ergebnis)
;;     (if (= tiefe 0)
;;         ergebnis
;;         (/ (N_i 1) (+ (D_i 1)
;;                       (iter (lambda (i) (D_i (+ i 1)))
;;                             (lambda (i) (N_i (+ i 1)))
;;                             (- tiefe 1)
;;                             ergebnis)))))
;;   (iter D_i N_i tiefe 0))
;; (define (phi tiefe)
;;   (/ 1 (ketten-bruch-iter (lambda (i) 1.0)
;;                      (lambda (i) 1.0)
;;                      tiefe)))
;; (phi 100)

;; ----------------------------------

;; e1p38
;; (define (ketten-bruch-iter D_i N_i tiefe)
;;   (define (iter D_i N_i tiefe ergebnis)
;;     (if (= tiefe 0)
;;         ergebnis
;;         (/ (N_i 1) (+ (D_i 1)
;;                       (iter (lambda (i) (D_i (+ i 1)))
;;                             (lambda (i) (N_i (+ i 1)))
;;                             (- tiefe 1)
;;                             ergebnis)))))
;;   (iter D_i N_i tiefe 0))

;; (define (compute-e tiefe)
;;   (define (N_i i)
;;     1.0)
;;   (define (D_i i)
;;     (cond ((< i 3) i)
;;           (else
;;            (if (= (remainder i 3) 2)
;;                (* 2 (+ (/ (- i 2) 3) 1))
;;                1))))
;;   (+ (ketten-bruch-iter D_i N_i tiefe) 2))

;; (compute-e 100)

;; ----------------------------------

;; e1p39
;; (define (ketten-bruch-iter D_i N_i tiefe)
;;   (define (iter D_i N_i tiefe ergebnis)
;;     (if (= tiefe 0)
;;         ergebnis
;;         (/ (N_i 1) (+ (D_i 1)
;;                       (iter (lambda (i) (D_i (+ i 1)))
;;                             (lambda (i) (N_i (+ i 1)))
;;                             (- tiefe 1)
;;                             ergebnis)))))
;;   (iter D_i N_i tiefe 0))
;; (define (tan-cf x k)
;;   (define (N_i i)
;;     (- (* 2 i) 1.0))
;;   (define (D_i i)
;;     (cond ((= i 1) x)
;;           (else (* x x))))
;;   (ketten-bruch-iter D_i N_i k))

;; (tan-cf (/ 3.1415 4) 100)

;; ----------------------------------

;; e1p40
;; (define (fixed-point f first-guess)
;;   (define tolerance 0.00001)
;;   (define (close-enough? v1 v2)
;;     (< (abs (- v1 v2)) tolerance))
;;   (define (try guess)
;;     (display guess)
;;     (newline)
;;     (let ((next (f guess)))
;;       (if (close-enough? guess next)
;;           next
;;           (try next))))
;;   (try first-guess))

;; (define (derivative f)
;;   (define dx 0.00001)
;;   (lambda (x) (/ (- (f (+ x dx)) (f x)) dx)))

;; (define (newton-transform f)
;;   (lambda (x) (- x (/ (f x) ((derivative f) x)))))

;; (define (newton f first-guess)
;;   (fixed-point (newton-transform f) first-guess))

;; (define (kubisch a b c)
;;   (lambda (x)
;;     (+ (* x x x) (* a x x) (* b x) c)))

;; (newton (kubisch 0 0 -8) 1)

;; ----------------------------------

;; e1p41
;; (define (doppelt f)
;;   (lambda (x) (f (f x))))
;; (((doppelt (doppelt doppelt)) inc) 5)

;; ----------------------------------

;; e1p42
;; (define (quadrat x)
;;   (* x x))
;; (define (komposition f g)
;;   (lambda (x) (f (g x))))
;; ((komposition quadrat inc) 6)

;; ----------------------------------

;; e1p43
;; (define (quadrat x)
;;   (* x x))
;; (define (komposition f g)
;;   (lambda (x) (f (g x))))

;; (define (n-fach f n)
;;   (if (= n 1)
;;       f
;;       (komposition f (n-fach f (- n 1)))))
;; ((n-fach quadrat 2) 5)

;; ----------------------------------

;; e1p44
;; (define (komposition f g)
;;   (lambda (x) (f (g x))))

;; (define (n-fach f n)
;;   (if (= n 1)
;;       f
;;       (komposition f (n-fach f (- n 1)))))
;; (define (glaetten f)
;;   (let ((dx 0.0001))
;;     (lambda (x) (/ (+ (f (- x dx)) (f x) (f (+ x dx))) 3))))
;; (define (n-glaetten f n)
;;   ((n-fach glaetten n) f))
;; ((glaetten (lambda (x) (* x x))) 3)
;; ((n-glaetten (lambda (x) (* x x)) 10) 3)

;; ----------------------------------

;; e1p45
;; (define (komposition f g)
;;   (lambda (x) (f (g x))))
;; (define (n-fach f n)
;;   (if (= n 1)
;;       f
;;       (komposition f (n-fach f (- n 1)))))
;; (define (average x y)
;;   (/ (+ x y) 2))
;; (define (average-damping f)
;;   (lambda (x) (average x (f x))))

;; (define (fixed-point f first-guess)
;;   (define tolerance 0.00001)
;;   (define (close-enough? v1 v2)
;;     (< (abs (- v1 v2)) tolerance))
;;   (define (try guess)
;;     (display guess)
;;     (newline)
;;     (let ((next (f guess)))
;;       (if (close-enough? guess next)
;;           next
;;           (try next))))
;;   (try first-guess))

;; (define (wurzel n x damping-times)
;;   (fixed-point ((n-fach average-damping damping-times) (lambda (y) (/ x (expt y (- n 1))))) 1.0))

;; (wurzel 12 100000 4)

;; ----------------------------------

;; e1p46
;; (define (iteratives-verbessern condition-satisfied? verbessern)
;;   (lambda (x)
;;     (let ((next (verbessern x)))
;;       (if (condition-satisfied? x next)
;;           next
;;           (verbessern next)))))
;; (define (close-enough? x1 x2)
;;   (define tolerence 0.00001)
;;   (< (abs (- x1 x2)) tolerence))
;; (define (wurzel-of-x-verbessern x)
;;   (lambda (wurzel)
;;     (/ (+ wurzel (/ x wurzel)) 2)))
;; (define (square-wurzel x)
;;   ((iteratives-verbessern close-enough? (wurzel-of-x-verbessern x)) 1.0))
;; (square-wurzel 2.0)

;; (define (fixed-point f)
;;   (iteratives-verbessern close-enough? f))

;; (define (square-root x)
;;   (define (g x)
;;     (lambda (y) (- (* y y) x)))
;;   (define (derivative f)
;;     (define dx 0.00001)
;;     (lambda (x) (/ (- (f (+ x dx)) (f x)) dx)))
;;   ((fixed-point (lambda (y) (- y (/ ((g x) y) ((derivative (g x)) y))))) 1.0))
;; (square-root 2.0)
