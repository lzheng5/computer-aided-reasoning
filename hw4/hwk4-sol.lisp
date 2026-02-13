(in-package "ACL2S")
(set-gag-mode nil)

; (modeling-start)

(set-induction-depth-limit 1)
(set-termination-method :measure)

(modeling-admit-all)

;; Q1
;; Q1a
;; Page !!!


;; Q1b
(definec m-bad-app (x y :tl acc :all)
  :nat
  (match (list x y)
    ((nil nil) 0)
    ((& nil) (+ 1 (len x)))
    ((nil (& . &)) (len y))
    (& (+ 2 (len x) (len acc)))))

;; Q1c
(property bad-app-1 (x y acc :tl)
  (implies
   (and (consp x)
        (endp y))
   (< (m-bad-app y x acc)
      (m-bad-app x y acc))))

(property bad-app-2 (x y acc :tl)
  (implies
   (and (endp x)
        (consp y))
   (< (m-bad-app x (rest y) (cons (first y) acc))
      (m-bad-app x y acc))))

(property bad-app-3 (x y acc :tl)
  (implies
   (and (consp x)
        (consp y))
   (< (m-bad-app x nil (m-bad-app acc nil y))
      (m-bad-app x y acc))))

(property bad-app-4 (x y acc :tl)
  (implies
   (and (consp x)
        (consp y))
   (< (m-bad-app acc nil y)
      (m-bad-app x y acc))))

(definec bad-app (x y acc :tl)
  :tl
  (declare (xargs :measure (m-bad-app x y acc)))
  (match (list x y)
    ((nil nil) acc)
    ((& nil) (bad-app y x acc))
    ((nil (f . r)) (bad-app x r (cons f acc)))
    (& (bad-app x nil (bad-app acc nil y)))))

;; Q1d
(property bad-app-nil-nil-acc (acc :tl)
  (== (bad-app nil nil acc) acc))

(property bad-app-x-nil-acc (x acc :tl)
  (implies (consp x)
           (== (bad-app x nil acc)
               (bad-app nil x acc))))

;; Checked with Pete. It is alright to use [append] instead of [app].
(property bad-app-nil-y-acc (x y acc :tl)
  (implies (endp x)
           (== (bad-app x y acc)
               (append (rev y) acc)))
    :hints (("goal" :induct (bad-app x y acc))))

(property bad-app-cons-y-nil (x y acc :tl)
  (implies (and (consp x)
                (endp acc))
           (== (bad-app x y acc)
               (append (rev x) y)))
    :hints (("goal" :induct (bad-app x y acc))))

(property bad-app-x-y-nil (x y :tl)
  (== (bad-app x y nil)
      (if (endp x)
          (rev y)
          (append (rev x) y))))

;; Q2

;; Q2a
;; Page 128

;; Q2b
(definec m-ack (n :nat m :all)
  :lex
  (if (natp m) (list n m) n))

;; Q2c
(property m-ack-1 (n m :nat)
    (implies
     (and (not (zp n))
          (zp m))
     (l< (m-ack (1- n) m)
         (m-ack n m))))

(property m-ack-2 (n m :nat)
    (implies
     (and (not (zp n))
          (not (zp m)))
     (l< (m-ack n (1- m))
         (m-ack n m))))

(property m-ack-3 (n m :nat)
    (implies
     (and (not (zp n))
          (not (zp m)))
     (l< (m-ack (1- n) (m-ack n (1- m)))
         (m-ack n m))))

(definec ack (n m :nat)
  :pos
  :skip-tests t ; ack is slow, so skip testing
  (declare (xargs :measure (m-ack n m)))
  (match (list n m)
    ((0 &) (1+ m))
    ((& 0) (ack (1- n) 1))
    (& (ack (1- n) (ack n (1- m))))))

;; Q3
(defdata if-atom (or bool var))
(defdata if-expr (or if-atom (list 'if if-expr if-expr if-expr)))
(defdata norm-if-expr (or if-atom (list 'if if-atom norm-if-expr norm-if-expr)))
(defdata-subtype-strict norm-if-expr if-expr)

;; Q3a
;; Page !!!

;; Q3b
;; Consulted Claude
(definec m-if-flat (x :if-expr) :pos
  (match x
    (:if-atom 1)
    (('if a b c)
     (* (m-if-flat a)
        (+ 1 (m-if-flat b) (m-if-flat c))))))

;; Q3c
(property m-if-flat-1 (x :if-expr)
  (implies
   (and (consp x)
        (eq (car x) 'if)
        (consp (cdr x))
        (consp (cdr (cdr x)))
        (consp (cdr (cdr (cdr x))))
        (eq (cdr (cdr (cdr (cdr x)))) nil)
        (let ((a (car (cdr x))))
          (if-atomp a)))
   (let ((b (car (cdr (cdr x)))))
     (l< (m-if-flat b)
         (m-if-flat x)))))

(property m-if-flat-2 (x :if-expr)
  (implies
   (and (consp x)
        (eq (car x) 'if)
        (consp (cdr x))
        (consp (cdr (cdr x)))
        (consp (cdr (cdr (cdr x))))
        (eq (cdr (cdr (cdr (cdr x)))) nil)
        (let ((a (car (cdr x))))
          (if-atomp a)))
   (let ((c (car (cdr (cdr (cdr x))))))
     (l< (m-if-flat c)
         (m-if-flat x)))))

(property m-if-flat-3 (x :if-expr)
  (implies
   (and (consp x)
        (eq (car x) 'if)
        (consp (cdr x))
        (consp (cdr (cdr x)))
        (consp (cdr (cdr (cdr x))))
        (eq (cdr (cdr (cdr (cdr x)))) nil)
        (let ((a (car (cdr x))))
          (and (consp a)
               (eq (car a) 'if)
               (consp (cdr a))
               (consp (cdr (cdr a)))
               (consp (cdr (cdr (cdr a))))
               (eq (cdr (cdr (cdr (cdr a)))) nil))))
   (let ((a (car (cdr x)))
         (b (car (cdr (cdr x))))
         (c (car (cdr (cdr (cdr x))))))
     (let ((d (car (cdr a)))
           (e (car (cdr (cdr a))))
           (f (car (cdr (cdr (cdr a))))))
       (l< (m-if-flat `(if ,d (if ,e ,b ,c) (if ,f ,b ,c)))
           (m-if-flat x))))))

(definec if-flat (x :if-expr) :norm-if-expr
  (declare (xargs :measure (m-if-flat x)))
  (match x
    (:if-atom x)
    (('if a b c)
     (match a
       (:if-atom `(if ,a ,(if-flat b) ,(if-flat c)))
       (('if d e f)
        (if-flat `(if ,d (if ,e ,b ,c) (if ,f ,b ,c))))))))

;; Q3d
(defdata if-assign (alistof var bool))

; Notice that if var is not in the if-assign, we return nil.
(definec lookup-var (var :var a :if-assign) :bool
  (match a
    (nil nil)
    (((!var . val) . &) val)
    (& (lookup-var var (cdr a)))))

(definec lookup-atom (e :if-atom a :if-assign) :bool
  (match e
    (:bool e)
    (& (lookup-var e a))))

(definec if-eval (e :if-expr a :if-assign) :bool
  (match e
    (:if-atom (lookup-atom e a))
    (('if x y z)
     (if (if-eval x a) (if-eval y a) (if-eval z a)))))

;; how come this type of goal showed up and cannot be refuted automatically ???
(property bad-if-eval (x y :all a :if-assign)
  (implies (and (not (consp x))
                (if-exprp (list* 'if x y))
                (consp y)
                (consp (cdr y))
                (not (cddr y))
                (not (booleanp x))
                (not (varp x))
                (if-assignp a))
           (not (if-eval (list* 'if x y) a))))

(property if-flat-equal-if (x :if-expr a :if-assign)
  (== (if-eval (if-flat x) a) (if-eval x a))
  :hints (("goal" :induct (if-flat x))))

;; Q3e
(definec assignedp (e :if-atom a :if-assign) :bool
  (or (boolp e)
      (consp (assoc-equal e a))))

(definec validp (e :norm-if-expr a :if-assign) :bool
  (match e
    (:if-atom (lookup-atom e a))
    (('if x y z)
     (if (assignedp x a)
         (if (lookup-atom x a)
             (validp y a)
             (validp z a))
       (and (validp y (acons x t a))
            (validp z (acons x nil a)))))))

(definec check-validp (e :if-expr) :bool
  (validp (if-flat e) nil))

(property validp-sound-var (x :norm-if-expr a :if-assign)
  (implies
   (and (if-atomp x)
        (lookup-atom x a))
   (== (validp x a) (if-eval x a))))

(definec agrees-with (b a :if-assign) :bool
   (match a
     (nil t)
     (((v . val) . rst)
      (and (== (lookup-var v b) val)
           (agrees-with b rst)))))

(property agrees-with-lookup (a b :if-assign x :if-atom)
  (implies
   (and (agrees-with b a)
        (assignedp x a))
   (== (lookup-atom x a)
       (lookup-atom x b))))

(property agrees-with-acons (a b :if-assign x :var v :bool)
  (implies
   (and (agrees-with b (acons x v a))
        (== (lookup-atom x b) v))
   (agrees-with b a)))

(property agrees-with-acons-2 (a b :if-assign x :var v :bool)
  (implies
   (and (agrees-with b a)
        (== (lookup-atom x b) v))
   (agrees-with b (acons x v a))))

(property validp-sound (e :norm-if-expr a b :if-assign)
  (implies
   (and (validp e a)
        (agrees-with b a))
   (if-eval e b))
  :hints (("goal" :induct (validp e a))))

(property check-validp-is-sound (e :if-expr a :if-assign)
  (implies (check-validp e) (if-eval e a)))
