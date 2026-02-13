(in-package "ACL2S")
(set-gag-mode nil)

; (modeling-start)

(set-induction-depth-limit 1)
(set-termination-method :measure)

(modeling-admit-all)

;; Q1
;; Checked with Pete. It is alright to use [append] instead of [app].
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
