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

(defthm test1
  (rels-of-proper-len (list (make-rel 'a 
                                      '(nil (0) (0 1) nil (0 1 2 3 4)))
                            (make-rel 'b 
                                      '(nil (0) (0 1 2) nil (0 1 2))))
                      5))

(defthm test2 
  (not (rels-of-proper-len (list (make-rel 'a 
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
  (rels-of-proper-len (list (make-rel 'a
                                      '(nil (0) (0 1) nil (0 1 2 3 4))))
                      5))

(defthm test8
  (not (rels-of-proper-len
        (list (make-rel 'foo '(nil (0) (0 1) nil (0 1 2 3 4))))
        4)))

(defthm test12
  (rels-well-formed (list (make-rel 'a '(nil (0) (0 1) nil (0 1 2 3 4))))
                    5))

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






