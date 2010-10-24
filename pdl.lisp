; A formalization of propositional dynamic logic (with finite frames) in ACL2.
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



(in-package "ACL2")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; FRAMES, MODELS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; So each relation is a list of list of integers, the ith element of which
; specifies the list of arcs coming out of node i (each element in the list
; that's the ith element of the relation will be an integer uniquely
; representing the destination node). The name of the relation must be a
; symbol.
(defun make-rel (name edges)
  (cons name edges))
(defun get-rel-name (rel) (car rel))
(defun get-rel-nodes (rel) (cdr rel))

; a list of these rel's is an association list with names as values.

; convenience functions for making a frame and getting its two
; components. Num-nodes has to be an integer; atomic-program-extensions should
; be a list of rels (each of which is made by make-rel).
(defun make-frame (num-nodes atomic-program-extensions)
  (list num-nodes atomic-program-extensions))
(defun get-num-nodes (f) (nth 0 f))
(defun get-atomic-programs (f) (nth 1 f))

; takes an assoc list of rels and an int l. returns t if the relations in the
; assoc list (i.e. the cdr of each elem) are all of the length l, nil
; otherwise.
(defun rels-of-proper-len (rels l)
  (if (endp rels)
      t
    (if (equal (len (get-rel-nodes (car rels))) l)
        (rels-of-proper-len (cdr rels) l)
      nil)))

(defun integer-list-listp (li)
  (if (endp li)
      t
    (and (integer-listp (car li))
         (integer-list-listp (cdr li)))))

; returns t if ali is an associative list mapping to true-listp's of
; true-listp's of integers. That is, the codomain of the alist is lists of
; lists of integers.
(defun integer-list-list-alistp (ali)
  (if (endp ali)
      t
    (if (consp (car ali))
        (and (integer-list-listp (cdar ali))
             (integer-list-list-alistp (cdr ali)))
      nil)))

(defun rels-well-formed (rels len)
  (and (rels-of-proper-len rels len)
       (integer-list-list-alistp rels)
       (symbol-alistp rels)))

; predicate function for frames. The relations must all have the appropriate
; number of nodes and format.
(defun framep (f)
  (and (integerp (get-num-nodes f))
       (rels-well-formed (get-atomic-programs f) (get-num-nodes f))))


; A valuation is going to be a list of lists of symbols. Element i in this list
; will enumerate those and only those propositional atoms which hold at world
; i. Each element of list i will be a list of symbols corresponding to atoms.
; 
; The parameter prop-atoms is a the set of all propositional atoms (so, \forall
; X \in valuation [ X \subseteq prop-atoms ]).
;
; Similarly, prog-atoms is the set of all atomic programs.
;
; we make a model from a frame and a valuation.
(defun make-model (frame valuation prop-atoms prog-atoms)
  (list frame valuation prop-atoms prog-atoms))
(defun get-frame (m) (nth 0 m))
(defun get-valuation (m) (nth 1 m))
(defun get-prop-atoms (m) (nth 2 m))
(defun get-prog-atoms (m) (nth 3 m))

; returns t if li is a list of true-listps of strings, nil otherwise.
(defun symbol-list-listp (li)
  (if (endp li)
      t
    (and (symbol-listp (car li))
         (symbol-list-listp (cdr li)))))

(defun valuation-syms-all-in-prop-atoms (v prop-atoms)
  (if (endp v)
      t
    (and (subsetp (car v) prop-atoms)
         (valuation-syms-all-in-prop-atoms (cdr v) prop-atoms))))

; predicate for valuations. This takes a valuation and an integer value
; representing the number of worlds each valuation should contain.
(defun proper-valuationp (v len prop-atoms)
  (and (equal (len v) len)
       (symbol-list-listp v)
       (valuation-syms-all-in-prop-atoms v prop-atoms)))

; predicate for models. Has to have a valid frame and a valid valuation.
(defun modelp (m)
  (and (framep (get-frame m))
       (proper-valuationp (get-valuation m)
                          (get-num-nodes (get-frame m))
                          (get-prop-atoms m))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; FORMULAS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; following are somewhat based on Manolios's formulation of formulas for the
; mu calculus.

(defun pdl-symbolp (s)
  (and (symbolp s)
       (not (member s '(~ v ^ -> not 
                        diamond box 
                        true false 
                        union star compose)))))

(defun pdl-programp (p prog-atoms)
  (cond ((symbolp p)
         (and (pdl-symbolp p) (member p prog-atoms)))
        ((equal (len p) 2)
         (and (equal (first p) 'star)
              (pdl-programp (second p) prog-atoms)))
        ((equal (len p) 3)
         (let ((first (first p))
               (second (second p))
               (third (third p)))
           (and (member first '(union compose))
                (pdl-programp second prog-atoms)
                (pdl-programp third prog-atoms))))
        (t nil)))

(defun pdl-formulap (f prop-atoms prog-atoms)
  (cond ((symbolp f)
         (or (member f '(true false))
             (and (pdl-symbolp f) (member f prop-atoms))))
        ((equal (len f) 2)
         (and (equal (first f) '~)
              (pdl-formulap (second f) prop-atoms prog-atoms)))
        ((equal (len f) 3)
         (let ((first (first f))
               (second (second f))
               (third (third f)))
           (or (and (member first '(v ^ ->))
                    (pdl-formulap second prop-atoms prog-atoms)
                    (pdl-formulap third prop-atoms prog-atoms))
               (and (member first '(diamond box))
                    (pdl-programp second prog-atoms)
                    (pdl-formulap third prop-atoms prog-atoms)))))
        (t nil)))