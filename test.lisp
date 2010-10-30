; Some sanity tests for the various things defined elsewhere.
;
;   Copyright 2010 Karl Pichotta
;
;   Licensed under the Apache License, Version 2.0 (the "License");
;   you may not use this file except in compliance with the License.
;   You may obtain a copy of the License at
;
;       http://www.apache.org/licenses/LICENSE-2.0
;
;   Unless required by applicable law or agreed to in writing, software
;   distributed under the License is distributed on an "AS IS" BASIS,
;   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
;   See the License for the specific language governing permissions and
;   limitations under the License.


; note that the names of the theorems are completely meaningless.

(defthm test1
  (rels-are-proper-len (list (make-rel 'a 
                                      '(nil (0) (0 1) nil (0 1 2 3 4)))
                            (make-rel 'b 
                                      '(nil (0) (0 1 2) nil (0 1 2))))
                      5))

(defthm test2 
  (not (rels-are-proper-len (list (make-rel 'a 
                                           '(nil (0) (0 1) nil (0 1 2 3 4)))
                                 (make-rel 'b 
                                           '(nil (0 1 2) nil (0 1 2))))
                           5)))

(defthm test3
  (integer-list-list-alistp (acons 'a
                                   '((1) (2 3) nil)
                                   (acons 'b
                                          nil
                                          nil))))

(defthm test4
  (not (integer-list-list-alistp (acons "a"
                                        '(1 2 3)
                                        (acons "b"
                                               nil
                                               nil)))))

(defthm test5
  (integer-list-list-alistp
          (list (make-rel "a" '(nil (0) (0 1) nil (0 1 2 3 4))))))
      
(defthm test6
  (not (integer-list-list-alistp '(1 2 3))))

(defthm test7 
  (rels-are-proper-len (list (make-rel 'a
                                      '(nil (0) (0 1) nil (0 1 2 3 4))))
                      5))

(defthm test8
  (not (rels-are-proper-len
        (list (make-rel 'foo '(nil (0) (0 1) nil (0 1 2 3 4))))
        4)))

(defthm test12
  (rels-are-well-formed (list (make-rel 'a '(nil (0) (0 1) nil (0 1 2 3 4))))
                    5))

(defthm test12a
  (not (rels-are-well-formed
        (list (make-rel 'a '(nil (0) (0 1) nil (0 1 2 6 4))))
        5)))

(defthm test13
  (framep (make-frame 5
                      (list (make-rel 'a '(nil (0) (0 1) nil (0 1 2 3 4)))))))

(defthm test14
  (modelp (make-model
           (make-frame 5
                       (list (make-rel 'a '(nil (0) (0 1) nil (0 1 2 3 4)))))
           '((p) (p q) nil nil nil)
           '(p q r)
           '(a b))))

(defthm test14a
  (world-valid-in-model
   (make-model
    (make-frame 5
                (list (make-rel 'a '(nil (0) (0 1) nil (0 1 2 3 4)))))
    '((p) (p q) nil nil nil)
    '(p q r)
    '(a b))
   3))

(defthm test14a
  (world-valid-in-model
   (make-model
    (make-frame 5
                (list (make-rel 'a '(nil (0) (0 1) nil (0 1 2 3 4)))))
    '((p) (p q) nil nil nil)
    '(p q r)
    '(a b))
   3))

(defthm test14c
  (rel-extensions-have-appropriate-values
   (list (make-rel 'a '(nil (0) (0 1) nil (0 1 2 3 4))))
   5))

(defthm test14d
  (not (rel-extensions-have-appropriate-values
        (list (make-rel 'a '(nil (0) (0 1) nil (0 1 2 3 4))))
        3)))

(defthm test15
  (not (modelp (make-model
                (make-frame 5
                            (list (make-rel 'a '(nil (0) (0 1) nil (0 1 2 3 4)))))
                '((p) (p q a) nil nil nil)
                '(p q r)
                '(a b)))))

(defthm test16
  (not (modelp
        (make-model
         (make-frame 5
                     (list (make-rel 'a '(nil (0) (0 1) nil (0 1 2 3 4)))))
         '((p) (p q) nil nil)
         '(p q r)
         '(a b)))))

(defthm test17 (pdl-symbolp 'p))

(defthm test18 (not (pdl-symbolp 'v)))

(defthm test19
  (pdl-formulap 'p
                '(p q r)
                '(a b c)))

(defthm test20 (not (pdl-formulap 'p nil nil)))

(defthm test21 (not (pdl-formulap 'v
                                  '(p q r)
                                  '(a b c))))

(defthm test22 
  (pdl-formulap '(diamond a p)
                '(p q r)
                '(a b c)))

(defthm test23
  (pdl-formulap '(-> q p)
                '(p q r)
                '(a b c)))

(defthm test24
  (pdl-formulap '(^ p r)
                '(p q r)
                '(a b c)))

(defthm test25
  (not (pdl-formulap '(v a p)
                     '(p q r)
                     '(a b c))))

(defthm test26
  (pdl-formulap '(box (union a b) p)
                '(p q r)
                '(a b c)))

(defthm test27
  (pdl-formulap '(box (union a (compose b (star c)))
                      (v p (^ q (~ r))))
                '(p q r)
                '(a b c)))

(defthm test28
  (not (pdl-formulap '(box (union a (compose b (star c)))
                           (v p (^ q (~ r p))))
                     '(p q r)
                     '(a b c))))



;semantics

(defthm stest1
  (pdl-satisfies
   (make-model
    (make-frame 5
                (list (make-rel 'a '(nil (0) (0 1) nil (0 1 2 3 4)))))
    '((p) (p q) nil nil nil)
    '(p q r)
    '(a b))
   0
   'p))

(defthm stest2
  (pdl-satisfies
   (make-model
    (make-frame 5
                (list (make-rel 'a '(nil (0) (0 1) nil (0 1 2 3 4)))))
    '((p) (p q) nil nil nil)
    '(p q r)
    '(a b))
   3
   'true))

(defthm stest3
  (pdl-satisfies
   (make-model
    (make-frame 5
                (list (make-rel 'a '(nil (0) (0 1) nil (0 1 2 3 4)))))
    '((p) (p q) nil nil nil)
    '(p q r)
    '(a b))
   0
   '(v p q)))


(defthm stest4
  (pdl-satisfies
   (make-model
    (make-frame 5
                (list (make-rel 'a '(nil (0) (0 1) nil (0 1 2 3 4)))))
    '((p) (p q) nil nil nil)
    '(p q r)
    '(a b))
   0
   '(~ q)))


(defthm stest5
  (pdl-satisfies
   (make-model
    (make-frame 5
                (list (make-rel 'a '(nil (0) (0 1) nil (0 1 2 3 4)))))
    '((p) (p q) nil nil nil)
    '(p q r)
    '(a b))
   4
   '(~ q)))

(defthm stest6
  (not
   (pdl-satisfies
    (make-model
     (make-frame 5
                 (list (make-rel 'a '(nil (0) (0 1) nil (0 1 2 3 4)))))
     '((p) (p q) nil nil nil)
     '(p q r)
     '(a b))
    4
    'q)))

; not theorems -- these are just there to examine the output.

; should be nil
(pdl-prog-value
 (make-model
  (make-frame 5
              (list (make-rel 'a '(nil (0) (0 1) nil (0 1 2 3 4)))
                    (make-rel 'b '((4) nil nil (0) (0)))))
  '((p) (p q) nil nil nil)
  '(p q r)
  '(a b))
 'a)

(pdl-prog-value
 (make-model
  (make-frame 5
              (list (make-rel 'a '(nil (0) (0 1) nil (0 1 2 3 4)))
                    (make-rel 'b '((4) nil nil (0) (0)))))
  '((p) (p q) nil nil nil)
  '(p q r)
  '(a b))
 '(star a))


(pdl-prog-value
 (make-model
  (make-frame 5
              (list (make-rel 'a '(nil (0) (0 1) nil (0 1 2 3 4)))
                    (make-rel 'b '((4) nil nil (0) (0)))))
  '((p) (p q) nil nil nil)
  '(p q r)
  '(a b))
 '(union a b))

(pdl-prog-value
 (make-model
  (make-frame 5
              (list (make-rel 'a '(nil (0) (0 1) nil (0 1 2 3 4)))
                    (make-rel 'b '((4) nil nil (0) (0)))))
  '((p) (p q) nil nil nil)
  '(p q r)
  '(a b))
 '(compose a b))

(defthm stest10
  (pdl-satisfies-symbol
   (make-model
    (make-frame 5
                (list (make-rel 'a '(nil (0) (0 1) nil (0 1 2 3 4)))
                      (make-rel 'b '((4) nil nil (0) (0)))))
    '((p) (p q) nil nil nil)
    '(p q r)
    '(a b))
   0
   'p))



(defthm stest11
  (not
   (pdl-satisfies
    (make-model
     (make-frame 5
                 (list (make-rel 'a '(nil (0) (0 1) nil (0 1 2 3 4)))
                       (make-rel 'b '((4) nil nil (0) (0)))))
     '((p) (p q) nil nil nil)
     '(p q r)
     '(a b))
    1
    '(^ p q))))
  

;t
(pdl-satisfies
 (make-model
  (make-frame 5
              (list (make-rel 'a '(nil (0) (0 1) nil (0 1 2 3 4)))
                    (make-rel 'b '((4) nil nil (0) (0)))))
  '((p) (p q) nil nil nil)
  '(p q r)
  '(a b))
 2
 '(diamond a q))





(pdl-satisfies
 (make-model
  (make-frame 5
              (list (make-rel 'a '(nil (2) (1) nil (0 1 2 3 4)))
                    (make-rel 'b '((4) nil nil (0) (0)))))
  '((p) (p q) nil nil nil)
  '(p q r)
  '(a b))
 2
 '(diamond a (diamond a p)))


(mutual-recursion
 (defun foo (a b)
   (if (consp a)
       (bar '(0 1 2 3) b)
     nil))
 (defun bar (x y)
   (if (consp x)
       (bar (cdr x) y)
       (if (pdl-satisfies m (car p-accessible-worlds) f)
           t
         (pdl-satisfies-diamond m (cdr p-accessible-worlds) f))
     nil)))



; termination analysis doesn't terminate.
(mutual-recursion
 (defun foo (x)
   (declare (xargs :measure (acl2-count x)))
   (cond ((endp x) nil)
         ((equal (len x) 1) (foo (cdr x)))
         (t (bar '(0 1 2) (car x)))))
 (defun bar (a b)
   (declare (xargs :measure (acl2-count a)))
   (if (consp a)
       (if (foo b) t (bar (cdr a) b))
     nil)))


(include-book "ordinals/lexicographic-ordering" :dir :system)
(encapsulate
 ()
 (set-well-founded-relation l<) ; will be treated as LOCAL
 (mutual-recursion
  (defun foo (x)
    (declare (xargs :measure (list (acl2-count x) 1)))
    (cond ((endp x) nil)
          ((equal (len x) 1) (foo (cdr x)))
          (t (bar '(0 1 2) (car x)))))
  (defun bar (a b)
    (declare (xargs :measure (list (acl2-count a) 0)))
    (if (consp a)
        (if (foo b) t (bar (cdr a) b))
      nil))))
 


(include-book "ordinals/lexicographic-ordering" :dir :system)
(encapsulate
 ()
 (set-well-founded-relation l<) ; will be treated as LOCAL
 (mutual-recursion
  (defun foo (m x)
    (declare (xargs :measure (list (len x) (len m))))
    (cond ((endp x) nil)
          ((equal (len x) 1) (foo m (cdr x)))
          (t (bar m (cdr m) x))))
  (defun bar (m a c)
    (declare (xargs :measure (list (len c) (len a))))
    (if (consp a)
        (if (foo m (car c)) t (bar m (cdr a) c))
      nil))))