(in-package "ACL2S")

;; Ex 14

;; (make-ord exp coeff rest) => ((exp . coeff) . rest)

(let* ((w1 (make-ord (o^ (make-ord 1 1 1) 2) 1 0))
       (w21 (o+ (make-ord 1 1 0) (make-ord 1 12 0)))
       (w22 (o+ (make-ord (make-ord 1 1 1) 1 0)
                (make-ord 2 9 0)))
       (w2 (make-ord (o* w21 w22) 1 0)))
  (o* w1 w2))

;; => ((((((1 . 1) . 1) . 1) (3 . 9) . 0) . 1) . 0)

(equal '((((((1 . 1) . 1) . 1) (3 . 9) . 0) . 1) . 0)
       '((((((1 . 1) . 1) . 1) . ((3 . 9) . 0)) . 1) . 0))

;; => t

;; '((((((1 . 1) . 1) . 1) . ((3 . 9) . 0)) . 1) . 0)

(equal
 (make-ord (make-ord (make-ord 1 1 1) 1 (make-ord 3 9 0)) 1 0)
 '((((((1 . 1) . 1) . 1) (3 . 9) . 0) . 1) . 0))

;; => t

;; w^(w^(w + 1) + (w^3 * 9))
