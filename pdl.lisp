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


; So this is a formalization of a finite version of Propositional Dynamic
; Logic. Right now it's actually PDL as given in Blackburn et al, so it doesn't
; have tests (the ? operator). We'll maybe want to try adding in tests later
; (since they do increase the expressivity of the language). 
; 
; Also, we are constrained to have finite frames, a finite number of atomic
; programs, and a  finite number of propositional variables (since represent
; each of the above as lists). There is, nonetheless, no shortage of
; interesting things to prove about the language, even given it has no tests
; and a finite number of worlds and atomic programs.


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
(defun rels-are-proper-len (rels l)
  (if (endp rels)
      t
    (if (equal (len (get-rel-nodes (car rels))) l)
        (rels-are-proper-len (cdr rels) l)
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

; takes a single list of ints, returns nonnil iff they're all natural numbers
; which are less than len (this corresponds to each outgoing arc in a part of a
; relation going to a node that actually exists in our model).
(defun indiv-rel-node-has-appropriate-values (rel-node len)
  (if (consp rel-node)
      (if (and (natp (car rel-node))
               (< (car rel-node) len))
          (indiv-rel-node-has-appropriate-values (cdr rel-node) len)
        nil)
    t))

; takes a single list of rel-nodes (the list of lists of ints) and the number
; of worlds in the model (len), returns t if all values in rel-nodes are
; appropriate, and nil otherwise.
(defun indiv-rel-has-appropriate-values (rel-nodes len)
  (if (consp rel-nodes)
      (if (indiv-rel-node-has-appropriate-values (car rel-nodes) len)
          (indiv-rel-has-appropriate-values (cdr rel-nodes) len)
        nil)
    t))

; takes the alist of relations (mapping symbols to lists of lists of ints)
; and ensures each value on the "inside" (the ints at the bottom of the
; structure) take appropriate values (that is for each int X in the innermost
; list, 0 <= X < len). Len is the number of worlds.
(defun rel-extensions-have-appropriate-values (rels len)
  (if (endp rels)
      t
    (if (indiv-rel-has-appropriate-values (get-rel-nodes (car rels)) len)
        (rel-extensions-have-appropriate-values (cdr rels) len)
      nil)))

(defun rels-are-well-formed (rels len)
  (and (rels-are-proper-len rels len)
       (integer-list-list-alistp rels)
       (symbol-alistp rels)
       (rel-extensions-have-appropriate-values rels len)))

; predicate function for frames. The relations must all have the appropriate
; number of nodes and format.
(defun framep (f)
  (and (integerp (get-num-nodes f))
       (rels-are-well-formed (get-atomic-programs f) (get-num-nodes f))))


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

; takes a model m and a world w and returns t if w represents a valid world in
; m, nil otherwise. We represent a world just as an integer -- it must be less
; than the number of worlds in the model.
(defun world-valid-in-model (m w)
  (and (integerp w)
       (< w (get-num-nodes (get-frame m)))))

; takes a model m and a world w and returns the list of propositional atoms
; which hold at that particular world. Assumes m is wellformed (i.e. (modelp
; m)) and w is appropriate for it (i.e. (world-valid-in-model m w)).
(defun get-prop-atoms-true-at-world (m w)
  (nth w (get-valuation m)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; SYNTAX
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



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; SEMANTICS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; PROGRAMS

; this takes an integer and a list of list of ints. The integer (world-index)
; corresponds to the world in rels (nth world-index rels) that we're taking the
; transitive closure of. This may return duplicates (e.g. '(0 0) instead of
; '(0)).
(defun transitive-closure (world-index rels)
  (let ((world-rel (nth world-index rels)))
    (if (consp world-rel)
        (let ((new-rels (update-nth world-index
                                    (cdr world-rel)
                                    rels)))
          (cons (car world-rel) 
                      (append (transitive-closure world-index
                                                  new-rels)
                              (transitive-closure (car world-rel)
                                                  new-rels))))
      world-rel)))

; so the variable r doesn't really do anything here but make the termination
; proof straightforward (structural induction vs. induction on a natp). the
; variable i here is the index of the world (in entire-r) that we're currently
; examining.
(defun rel-star-with-index (r i entire-r)
  (if (consp r)
      (cons (cons i (transitive-closure i entire-r))
            (rel-star-with-index (cdr r) (+ 1 i) entire-r))
    nil))

; takes a list of lists of ints, returns its reflexive transitive closure.
(defun rel-star (r)
  (rel-star-with-index r 0 r))

; takes a list of lists of ints, returns the list of unions (so if L1= <A B C>
; and L2 = <D E F>, this returns <AuD BuE CuF>).
(defun rel-union (r1 r2)
  (if (consp r1)
      (cons (append (car r1) (car r2))
            (rel-union (cdr r1) (cdr r2)))
    nil))

(defun composition-of-single-rel (rel r2)
  (if (consp rel)
      (cons (nth (car rel) r2)
            (composition-of-single-rel (cdr rel) r2))
    nil))

; r's only purpose is to help ACL2 figure out an easy termination proof. In
; reality, we're just using it as a structure s.t. (len r) + i = (len r1).
(defun rel-compose-with-index (r i r1 r2)
  (if (consp r)
      (cons (composition-of-single-rel (nth i r1) r2)
            (rel-compose-with-index (cdr r) (+ 1 i) r1 r2))
    nil))


(defun rel-compose (r1 r2)
  (rel-compose-with-index r1 0 r1 r2))


; defines the semantics of a program. Takes a model m and a program p (we
; assume that (modelp m) and (pdl-programp p)).
(defun pdl-prog-value (m p)
  (let ((f (get-frame m)))
    (cond ((symbolp p)
           (cdr (assoc p (get-atomic-programs f))))
          ((equal (len p) 2)
           (rel-star (pdl-prog-value m (second p))))
          ((equal (len p) 3)
           (let ((first (first p))
                 (second (second p))
                 (third (third p)))
             (cond ((equal first 'union)
                    (rel-union (pdl-prog-value m second)
                               (pdl-prog-value m third)))
                   ((equal first 'compose)
                    (rel-compose (pdl-prog-value m second)
                                 (pdl-prog-value m third))))))
          (t nil))))

; takes a model m, world w and program p and returns the p-accessible worlds
; from w in m.
(defun prog-accessible-worlds (m w p)
  (nth w (pdl-prog-value m p)))

  
; FORMULAS

;we assume m, w, f are wellformed.
(defun pdl-satisfies-symbol (m w f)
  (cond ((equal f 'true) t)
        ((equal f 'false) nil)
        (t (if (member f (get-prop-atoms-true-at-world m w))
               t
             nil))))

; Pointwise modal valuation. (pdl-satisfies M w phi) iff $M, w \models phi$.
; That is, if pdl formula f is satisfied at world w of model m, then this will
; return t, otherwise it will return nil.
;
; For now, we return nil if m, w, or f aren't valid. We may have to reassess
; this.
(mutual-recursion
 (defun pdl-satisfies (m w f)
   (if (and (modelp m)
            (world-valid-in-model m w)
            (pdl-formulap f
                          (get-prop-atoms m)
                          (get-prog-atoms m)))
       (cond ((symbolp f)
              (pdl-satisfies-symbol m w f))
             ((equal (len f) 2)
              (not (pdl-satisfies m w (second f))))
             ((equal (len f) 3)
              (cond ((equal (first f) 'v)
                     (or (pdl-satisfies m w (second f))
                         (pdl-satisfies m w (third f))))
                    ((equal (first f) 'diamond)
                     (pdl-satisfies-diamond
                      m w (prog-accessible-worlds m w (second f)) (third f)))))
             (t nil))
     nil))
 (defun pdl-satisfies-diamond (m w p-accessible-worlds f)
   (if (consp p-accessible-worlds)
       (if (pdl-satisfies m (car p-accessible-worlds) f)
           t
         (pdl-satisfies-diamond m w (cdr p-accessible-worlds) f))
     nil)))





;TODO function to translation from (box, diamond, ->, v, ^, ~) to (diamond,
;v,~).


;TODO could prove some basic statements about semantics, e.g.
; (iff (pdl-satisfies m w '(~ f)) (not (pdl-satisfies m w f))). These will be
; interesting if we do indeed end up only defining semantics for (~,v,<>).