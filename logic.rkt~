#lang racket
(require (lib "trace.ss"))

(define (variable? x) (symbol? x))
(define (isbound v θ) (pair? (assoc v θ)))
(define (get-binding var bindings) (assoc var bindings))
(define (binding-var binding) (car binding))
(define (binding-val binding) (cdr binding))
(define (make-binding var val) (cons var val))
(define (lookup var bindings) (binding-val (get-binding var bindings)))
(define (extend-bindings var val bindings)
  (cons (make-binding var val) bindings))
(define (occurs-in? var x bindings)
  (cond 
    [(eq? var x) #t]
    [(and (variable? x) (get-binding x bindings))
     (occurs-in? var (lookup x bindings) bindings)]
    [(pair? x) (or (occurs-in? var (car x) bindings)
                   (occurs-in? var (cdr x) bindings))]
    [else #f])
  )
(define (atom? x) (not (or (pair? x) (list? x))))
(define (reuse-cons x y x-y)
                    (if (and (eq? x (car x-y)) (eq? y (cdr x-y))) x-y (cons x y))
                    )

(define (first x)
  (if (pair? x) (car x) x))
(define (rest x)
  (if (pair? x) (cdr x) '()))
(define (subst-bindings bindings x)
  (cond
    [(eq? x '()) '()]
    [(eq? bindings #f) #f]
    [(eq? bindings '()) x]
    [(and (variable? x) (get-binding x bindings))
     (subst-bindings bindings (lookup x bindings))]
    [(atom? x) x]
    [else (reuse-cons (subst-bindings bindings (first x))
                      (subst-bindings bindings (rest x))
                      x)]))
(define (unify x y bindings)
  (cond 
    [(eq? bindings #f) #f]
    [(eq? x y) bindings]
    [(variable? x) (unify-var x y bindings)]
    [(variable? y) (unify-var y x bindings)]
    [(and (pair? x) (pair? y)) (unify (cdr x) (cdr y) (unify (car x) (car y) bindings))]
    [else #f])
  )

(define (unify-var var x bindings) 
  (cond [(get-binding var bindings)
         (unify (lookup var bindings) x bindings)]
        [(and (variable? x) (get-binding x bindings))
         (unify var (lookup x bindings) bindings)]
        [(occurs-in? var x bindings) #f]
        [else (extend-bindings var x bindings)])
  )

(define (replace-term a-list exp)
  (cond
    [(variable? exp) (let [(replacement (assoc exp a-list))] (if replacement (cdr replacement) exp))]
    [(pair? exp) (cons (replace-term a-list (car exp)) (replace-term a-list (cdr exp)))]
    [else (map (λ(x) (replace-term a-list x)) exp)]
  ))

(define (unifier x y)
  (instantiate x (unify x y '()))
  )

(define (instantiate x e)
  (subst-bindings e x)
  )
;;;;;;;;;;;;;;;;;;;;;;;;;; TEST UNIFY FUNCTION  ;;;;;;;;;;;;;;;;;;;;;;;;;
(trace unify unify-var extend-bindings occurs-in? subst-bindings)
;(unify '(X 3 Y) '((Y Z) Z 7) '())
;(unify '(john x) '(john y) '())
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; UNIT TESTS
;INPUT : (unify '(X 3 X) '(X 3 X) '())
;OUTPUT: '()
;
;INPUT : (unify '(X 3 X) '(Zee 3 Zee) '())
;OUTPUT: '((X . Zee)) or '((Zee . X))
;
;INPUT : (unify '(X 3 X) '(2 Y 2) '())
;OUTPUT: ((X . 2) (Y . 3))
;
;INPUT : (unify '(X 3 X) '(Z Y 2) '())
;OUTPUT: ((X . 2) (Y . 3) (Z . 2))
;
;INPUT : (unify '(X 3 Y) '(Z Y 2) '())
;OUTPUT: #f
;
;INPUT : (unify '(X 3 Y) '((Y Z) Z 7) '())
;OUTPUT: ((X 7 3) (Z . 3) (Y . 7))
(unifier '(X 3 Y) '((Y Z) Z 7))