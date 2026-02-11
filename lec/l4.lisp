#|

Copyright © 2026 by Pete Manolios 

Author: Pete Manolios
Date:   1/20/2026

Code used in lecture 4 of Computer-Aided Reasoning.  

|#

(in-package "ACL2S")

"Turn off testing since ack is very slow."
(acl2s-defaults :set :testing-enabled nil)

(definec ack (n m :nat) :pos
  (match (list n m)
    ((0 &) (1+ m))
    ((& 0) (ack (1- n) 1))
    (& (ack (1- n) (ack n (1- m))))))

"Here is an attempt to compute some small values of ack"

(time$ (ack 3 8))
(time$ (ack 3 9))
(time$ (ack 3 10))
(time$ (ack 3 11))
(time$ (ack 3 12))

"The execution time increasese exponentially.
One way to deal with this is via memoization
(dynamic programming)"

(memoize 'ack)

(time$ (ack 3 12))
(time$ (ack 3 13))
(time$ (ack 3 14))
(time$ (ack 3 15))

"Notice that we got a stack overflow."

"So, here is a challenge.
1. What is (mod (ack 3 123456789) 53217)
2. What is (mod (ack 3 123456789) (ack 3 21))

Ideas?
"

"Let's use ACL2s to speed up computation
via theorem proving.
As we discussed in the lecture, computation
is a very simple kind of inference and we
can interleave computation and theorem proving.
"

(ack 0 0)
(ack 0 1)
(ack 0 2)
(ack 0 3)

(property ack0 (m :nat)
  (= (ack 0 m) (1+ m)))


(ack 1 0)
(ack 1 1)
(ack 1 2)
(ack 1 3)

(property ack1 (m :nat)
  (= (ack 1 m) (+ m 2))
  :hints (("goal" :induct (nat-ind m))))

(ack 2 0)
(ack 2 1)
(ack 2 2)
(ack 2 3)

(property ack2 (m :nat)
  (= (ack 2 m) (+ 3 (* m 2)))
  :hints (("goal" :induct (nat-ind m))))

(ack 3 0)
(ack 3 1)
(ack 3 2)
(ack 3 3)

(property ack3 (m :nat)
  (= (ack 3 m) (- (expt 2 (+ m 3)) 3))
  :hints (("goal" :induct (nat-ind  m))))

"Or, we could have asked grok/..."

"Here is an attempt to directly compute (ack 3 15)"

(time$ (ack 3 15))

"Stack overflow. Let's use the theorems we proved."
(in-theory (disable (:executable-counterpart ack)))

(property (z :nat) (= (ack 3 15) z))

"Now let's find the answer to the challenge problem."

(property (z :nat) (= (mod (ack 3 123456789) 53217) z))
(property (z :nat) (= (mod (ack 3 123456789) (ack 3 21)) z))

"Or we could have asked grok.
Notice COP: chain of program, ie, the use of tools.
"

"How fast does ack grow?
Again, let's use ACL2s.
"

(property ack4 (m :nat)
  (= (ack 4 m)
     (if (zp m)
         (ack 3 1)
       (ack 3 (ack 4 (1- m))))))

(property ack3-lemma (m :nat)
  (< (expt 2 m) (ack 3 m)))

(property ack4-lemma (m :pos)
  (< (expt 2 (ack 4 (1- m)))
     (ack 4 m))
  :hints (("goal" :expand (ack 4 m)
           :in-theory (acl2::disable ack4 ack3))))

(property ()
  (< (expt 2 (ack 4 2)) (ack 4 3))
  :hints (("goal" :use (:instance ack4-lemma (m 3)))))

(property ()
  (< (* (expt 10 1000) (expt 10 1000)) (ack 4 2)))

"
The number of bits required to represent
the number n is about log n.

Now, (ack 4 3), as per above, is greater than
(expt 2 (ack 4 2))

So the number of bits required to represent

(ack 4 3)

is more than the number of bits required to represent

(expt 2 (ack 4 2)),

which is about (ack 4 2) bits.

The number of particles in the universe is estimated to
be between 10^78 and 10^81, but even if it is 10^1,000
and we had 10^1,000 universes at our disposal, and if
we could mark each of the particles in each of the
universes with a 0 or a 1, we still wouldn't have
enough particles to write down (ack 4 3) because
10^1,000 * 10^1,000 < (ack 4 2)

Also one can compute (ack 3 n) for very large n,
e.g., (property (z :nat) (= (ack 3 100000) z))
computes (ack 3 100000) in under a second.
"

(property (z :nat) (= (ack 3 100000) z))
(property (z :nat) (= (ack 4 2) z))

"Or we could ask grok"

(property (z :nat) (= (ack 4 2) (- (expt 2 65536) 3)))
