#lang racket
(require (lib "trace.ss"))

(require data/heap)
(define(A*-graph-search start goal? moves heuristic)
  (struct node (state pred move g h f))
  (define (node<=? x y) (<= (node-f x) (node-f y)))
  (define Q (make-heap node<=?))
  (define ht (make-hash))
  (define (not-in-hash? SAW) (eq? #f (hash-ref ht (get-hash (car SAW)) #f)))
  (define (print-solution anode)
    (cond
      [(null? anode)]
      [(null? (node-pred anode)) (list (list 'start (node-state anode) (node-g anode) (node-h anode) (node-f anode)))]
      [else (append (append (print-solution (node-pred anode))) (list (list (node-move anode) (node-state anode) (node-g anode) (node-h anode) (node-f anode))))]))
  (define (add-SAW-to-heap SAW prev)
    (let* [(weight (car (cdr (cdr SAW)))) (h (heuristic (car SAW))) (action (car (cdr SAW)))]
      (let [(g (if (null? prev) weight (+ weight (node-g prev))))]
        (define f (+ g h))
        (node (car SAW) prev action g h f))))
  (define (get-hash state) state)
  (define no-solution 'failure)
  
  (map (λ(x) (let [(h (heuristic x))] (heap-add! Q (node x '() 'start 0 h h)))) start)
  (let loop ()
    (define curr (heap-min Q))
    (hash-set! ht (get-hash (node-state curr)) curr)
    (heap-remove-min! Q)
    (cond
      [(goal? (node-state curr)) (print-solution curr)]
      [else
       (let ([SAWs (filter not-in-hash? (moves (node-state curr)))])
         (heap-add-all! Q (map (λ(x) (add-SAW-to-heap x curr)) SAWs)))
       (if (= (heap-count Q) 0) no-solution (loop))])))

(define (deduce definite-horn-clauses top-clauses)
  (define (variable? x) (symbol? x))
  (define (is-not? x) (eq? '¬ x))
  (define (is-not-term? x) (is-not? (first x)))
  (define (value x θ) (cdr (assoc x θ)))
  (define (isbound? v θ) (pair? (assoc v θ)))
  (define (get-binding var bindings) (assoc var bindings))
  (define (binding-var binding) (car binding))
  (define (binding-val binding) (cdr binding))
  (define (make-binding var val) (cons var val))
  (define (lookup var bindings) (binding-val (get-binding var bindings)))
  (define (extend-bindings var val bindings)
    (cons (make-binding var val) bindings))
  (define (atom? x) (not (or (pair? x) (list? x))))
  (define (reuse-cons x y x-y)
    (if (and (eq? x (car x-y)) (eq? y (cdr x-y))) x-y (cons x y))
    )
  (define (first x) (if (pair? x) (car x) x))
  (define (rest x) (if (pair? x) (cdr x) '()))
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
  (define (unify x y θ)
    (cond
      ((eq? θ #f) #f)
      ((and (variable? x)(isbound? x θ)) (unify (value x θ) y θ))
      ((and (variable? y)(isbound? y θ)) (unify x (value y θ) θ))
      ((eq? x y) θ)
      ((variable? x) (if (occur? x y θ) #f (cons (cons y x) θ)))
      ((variable? y) (if (occur? y x θ) #f (cons (cons y x) θ)))
      ((equal? x y) θ)
      ((not (and (pair? x)(pair? y))) #f)
      ((not (eq? (car x)(car y))) #f)
      ((not (= (length x)(length y))) #f)
      (else (foldl unify θ (cdr x)(cdr y)))))
  
  (define (occur? v x θ)
    (cond
      ((and (variable? x)(isbound? x θ)) (occur? v (value x θ) θ))
      ((eq? v x) #t)
      ((variable? v) #f)
      ((not (pair? x)) #f)
      (else (ormap (λ y (occur? v y θ)) (cdr x)))))
  
  (define (replace-term a-list exp)
    (cond
      [(variable? exp) (let [(replacement (assoc exp a-list))] (if replacement (cdr replacement) exp))]
      [(pair? exp) (cons (replace-term a-list (car exp)) (replace-term a-list (cdr exp)))]
      [else (map (λ(x) (replace-term a-list x)) exp)]
      ))
  (define (instantiate x e) (subst-bindings e x))
  (define (unique-find-anywhere-if exp found-so-far)
    (cond
      [(eq? exp '()) found-so-far]
      [else (if (atom? exp)
                (if (and (variable? exp) (not (member exp found-so-far))) (cons exp found-so-far) found-so-far)
                (unique-find-anywhere-if (rest (first exp)) (unique-find-anywhere-if (rest (rest exp)) found-so-far)))])
    )
  (define (freevarsin x) (unique-find-anywhere-if x '()))
  (define (rename-variables x) (subst-bindings (map (λ(y) (cons y (gensym y))) (freevarsin x)) x))
  (define (instantiate-clause c a) (map (λ(x) (instantiate x a)) c))
  (define (rename-clause c) (map (λ(x) (rename-variables x)) c))
  (define (freevarsin-clause c) (append (map (λ(x) (rename-variables x))c)))
  (define (unifier x y) (instantiate x (unify x (rename-variables y) '())))
  (define (resolve lc kd)
    (if (is-not-term? (first lc))
        (let* ([renamed-lc (rename-clause lc)] [unifiable (unify (first (rest (first renamed-lc))) (first kd) '())])
          (if unifiable (rename-clause (instantiate-clause (append (cdr renamed-lc) (cdr kd)) unifiable)) #f)
          )
        #f ))
  
  (define (res-moves s) 
    (filter-map 
     (λ(rhs) (let ([resolved (resolve s rhs)]) (if resolved (list resolved (first rhs) 1) #f))) 
     definite-horn-clauses) 
    )
  (define (res-heuristic s) 0)
  (define (res-goal? s) (eq? s '()))
  (A*-graph-search top-clauses res-goal? res-moves res-heuristic)
  )

;;;;;;;;;;;;;;;;;;;;;;;;;; TESTING ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define axioms1 '(
                  ((Criminal x) (¬(American x)) (¬(Weapon y)) (¬(Sells x y z)) (¬(Hostile z)))
                  ((Enemy (Nono) (America) ))
                  ((Owns (Nono) (M1) ))
                  ((Missile (M1) ))
                  ((Sells (West) x (Nono)) (¬(Missile x)) (¬(Owns (Nono) x)))
                  ((American (West) ))
                  ((Weapon x) (¬(Missile x)))
                  ((Hostile x) (¬(Hostile (Mother-of x) )))
                  ((Hostile x) (¬(Enemy x (America) )))
                  ((Hostile x) (¬(Hostile (Father-of x) )))
                  ))
(define conjs1 '(((¬(Criminal (West))))))

(define axioms2 '(
                  ((=(* x 1)x))
                  ((=(* 1 x)x))
                  ((=(* x (/x))1))
                  ((=(*(/ x)x)1))
                  ((=(* x w)v)(¬(=(* x y)u))(¬(=(* y z)w))(¬(=(* u z)v)))
                  ((=(* u z)v)(¬(=(* x y)u))(¬(=(* y z)w))(¬(=(* x w) v)))
                  ((=(* x x)1))
                  ((=(*(F) (G)) (H)))
                  ))
(define conjs2 '( ((¬(= (*(G) (F)) (H)))) ) )

(deduce axioms2 conjs2)
(deduce axioms1 conjs1) 
