#|

Author: Pete Manolios
Date:   2/24/2026

Code used in lecture 14 of Computer-Aided Reasoning.  

|#

(defun-sk E-Fz (u v)
  (exists z (equal (app u v) (rev z))))

#|

 This generates the following events, where e-fz-witness is a new
 function symbol, a Skolem function. 

 ; defun-nx introduces a non-executable function
 (defun-nx e-fz (u v) 
   (let ((z (e-fz-witness u v))) 
     (equal (app u v) (rev z))))

 In our slides, e-fz is Ez and e-fz-witness is Fz.

 Since we can't say that there exist a function s.t. ... in FO, we
 instead say that if

 (app u v) = (rev z) for any z, then (app u v) = (rev (e-fz-witness u v))

 So, we add the following constraint so that e-fz-witness is not just
 any function, but one restricted by e-fz-suff.

 (defthm e-fz-suff
   (implies (equal (app u v) (rev z))
            (e-fz u v)))

 Now, we can use ACL2s to reason about quantifiers. Typically, we do
 this by defining a function that provides the z above. Here is an
 example.

|#

:pe e-fz
:pf e-fz
:pf e-fz-suff
:pcb! :x

(definecd fz (u v :tl) :tl ; define a function that generates a witness
  (app (rev v) (rev u)))

(property fz-thm (u v :tl) ; show that fz works
  (== (rev (fz u v))
      (app u v))
  :hints (("Goal" :in-theory (enable fz))))

(property (u v :tl) ; prove an existential
  :check-contracts? nil
  (e-fz u v)
  :hints (("goal" :use ((:instance e-fz-suff (z (fz u v)))))))

; Proof builder version
(verify
 (implies (and (tlp u) (tlp v))
          (e-fz u v)))
 th
 pro
 th
 sr
 (r 1 ((z (fz u v))))
 th
 (dv 2)
 th
 sr
 r
 top
 th
 bash
 (undo 4)
 th
 bash
 (exit t)

(property foo (u v :tl) ; prove an existential
  :check-contracts? nil
  (e-fz u v)
  :instructions (:pro
                 (:rewrite e-fz-suff ((z (fz u v))))
                 :bash))
