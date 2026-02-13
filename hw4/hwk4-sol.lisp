(in-package "ACL2S")
(set-gag-mode nil)

(modeling-start)

(set-induction-depth-limit 1)
(set-termination-method :measure)

; (modeling-admit-all)

;; Q1
(definec m-bad-app (x y :tl acc :all)
  :nat
  (match (list x y)
    ((nil nil) 0)
    ((& nil) (+ 1 (len x)))
    ((nil (& . &)) (len y))
    (& (+ 2 (len x) (len acc)))))

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

;; Page 128

(definec m-ack (n :nat m :all)
  :lex
  (if (natp m) (list n m) n))

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

(definec if-depth (x :if-expr)
  :nat
  (cond ((if-atomp x) 0)
        ((eq (car x) 'if)
         (+ (cond ((if-atomp (cadr x)) 0)
                  (t 1))
            (if-depth (cadr x))))))

;; (definec if-cnt (x :if-expr)
;;   :nat
;;   (match x
;;     (:if-atom 0)
;;     (('if a b c)
;;      (+ (match a
;;           (:if-atom 0)
;;           (('if & & &) 1))      ;; Only add 1 if 'a' is an IF
;;         (* (expt 2 (if-cnt a))
;;            (+ (if-cnt b) (if-cnt c)))))))

(definec weight (x :if-expr)
  :nat
  (match x
    (:if-atom 1)
    (('if a b c) (+ 1 (weight a) (weight b) (weight c)))))

(definec m-if-flat1 (x :if-expr)
  :lex
  (match x
    (:if-atom 0)
    (('if a b c)
     (match a
       (:if-atom
        (+ (m-if-flat1 b) (m-if-flat1 c)))
       (('if d e f)
        1)))))

(set-termination-method :ccg)
(defdata rst (list nat nat))
(defdata-subtype-strict rst lex)
(definec m-if-flat3 (x :if-expr)
  :rst
  :skip-admissibilityp t
  (match x
    (:if-atom (list 0 1))
    (('if a b c)
     (let ((mb (m-if-flat2 b))
           (mc (m-if-flat2 c)))
       (match (list mb mc)
         (((& bs) (& cs))
          (match a
            (:if-atom
             (list 0 (+ bs cs)))
            (('if d e f)
             (let ((md (m-if-flat2 d))
                   (me (m-if-flat2 e))
                   (mf (m-if-flat2 f)))
               (match (list md me mf)
                 (((dd ds) (& es) (& fs))
                  (let ((nd (+ 1 dd)))
                    (list nd
                          (+ 1
                             (* (expt 2 nd) (+ bs cs))
                             ds es fs))))))))))))))

;; (definec m-if-flat (x :if-expr)
;;   :lex
;;   (list (if-cnt x) (weight x)))

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
       (l< (m-if-flat2 `(if ,d (if ,e ,b ,c) (if ,f ,b ,c)))
           (m-if-flat2 x))))))

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
     (l< (m-if-flat3 b)
         (m-if-flat3 x)))))

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

(definec if-flat (x :if-expr) :norm-if-expr
  (declare (xargs :measure (m-if-flat x)))
  ;; :skip-admissibilityp t
  (match x
    (:if-atom x)
    (('if a b c)
     (match a
       (:if-atom `(if ,a ,(if-flat b) ,(if-flat c)))
       (('if d e f)
        (if-flat `(if ,d (if ,e ,b ,c) (if ,f ,b ,c))))))))
