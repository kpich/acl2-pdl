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

(include-book "ordinals/lexicographic-ordering" :dir :system)

(set-gag-mode :goals)


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
       (not (member s '(~ v 
                        box 
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
           (or (and (equal first 'v)
                    (pdl-formulap second prop-atoms prog-atoms)
                    (pdl-formulap third prop-atoms prog-atoms))
               (and (equal first 'box)
                    (pdl-programp second prog-atoms)
                    (pdl-formulap third prop-atoms prog-atoms)))))
        (t nil)))


; so our syntax is richer than our semantics, which is defined only for
; negation and disjunction. this takes a formula that could have conjunction or
; implication and removes them. Also, if the formula has box, it translates it
; into a statement with its dual, diamond.
(defun simplify-formula (f)
  (cond ((atom f) f)
        ((equal (len f) 2)
         (list (car f) (simplify-formula (cdr f))))
        (t
         (let ((first (first f))
               (second (second f))
               (third (third f)))
           (cond ((equal first 'v)
                  (list 'v (simplify-formula second)
                        (simplify-formula third)))
                 ((equal first 'box)
                  (list 'box second (simplify-formula third)))
                 ((equal first 'diamond)
                  (list '~ 'box second (list '~ (simplify-formula third))))
                 ((equal first '^)
                  (list '~ (list 'v
                                 (list '~ (simplify-formula second))
                                 (list '~ (simplify-formula third)))))
                 ((equal first '->)
                  (list 'v
                        (list '~ (simplify-formula second))
                        (simplify-formula third)))
                 (t f))))))
             
    

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


(defun rel-star-with-index (i r)
  (declare (xargs :measure (nfix (- (len r) (nfix i)))))
  (if (< (nfix i) (len r))
      (cons (cons i (transitive-closure i r))
            (rel-star-with-index (+ 1 (nfix i)) r))
    nil))

; takes a list of lists of ints, returns its reflexive transitive closure.
(defun rel-star (r)
  (rel-star-with-index 0 r))

; takes a list of lists of ints, returns the list of unions (so if L1= <A B C>
; and L2 = <D E F>, this returns <AuD BuE CuF>).
(defun rel-union (r1 r2)
  (if (consp r1)
      (cons (append (car r1) (car r2))
            (rel-union (cdr r1) (cdr r2)))
    nil))

(defun composition-of-single-rel (rel r2)
  (if (consp rel)
      (append (nth (car rel) r2)
            (composition-of-single-rel (cdr rel) r2))
    nil))

(defun rel-compose (r1 r2)
  (if (consp r1)
      (cons (composition-of-single-rel (car r1) r2)
            (rel-compose (cdr r1) r2))
    nil))



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

(defun prog-accessible-worlds (m w p)
  (nth w (pdl-prog-value m p)))


;  (remove-duplicates (nth w (pdl-prog-value m p))))

  
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
; So the natural semantics here would use mutual recursion (and are given
; below). However, since mutual recursion is like basically impossible to
; reason about, we _actually_ define a basically equivalent function and use
; that for reasoning. So here's the first, mutually-recursive definition that
; we won't actually use:


(encapsulate
 ()
 (set-well-founded-relation l<) 
 (mutual-recursion
  (defun pdl-satisfies-mutual (m w f worlds)
    (declare (xargs :measure (list (acl2-count f) (acl2-count worlds))))
    (cond ((symbolp f)
           (pdl-satisfies-symbol m w f))
          ((equal (len f) 2)
           (not (pdl-satisfies-mutual m w (second f) worlds)))
          ((equal (len f) 3)
           (cond ((equal (first f) 'v)
                  (or (pdl-satisfies-mutual m w (second f) worlds)
                      (pdl-satisfies-mutual m w (third f) worlds)))
                 ((equal (first f) 'box)
                  (pdl-satisfies-box-mutual
                   m
                   (prog-accessible-worlds m w (second f))
                   (third f)))))
          (t nil)))
  (defun pdl-satisfies-box-mutual (m p-accessible-worlds f)
    (declare (xargs :measure (list (acl2-count f)
                                   (acl2-count p-accessible-worlds))))
    (if (consp p-accessible-worlds)
        (and (pdl-satisfies-mutual m (car p-accessible-worlds) f nil)
             (pdl-satisfies-box-mutual m (cdr p-accessible-worlds) f))
      t))))


; ...and here is the non-mutually-recursive equivalent that we WILL end up
; using (basically we just have another argument, evaling-formula, that is t if
; we're in pdl-satisfies-mutual above and nil if we're in pdl-satisfies-diamond
; above. That is, we changed
;
; (mutual-recursion (defun foo (A) foo-body) (defun bar (B) bar-body))
;
; to
; (defun foobar (A B C) (if C foo-body bar-body))

(defun pdl-satisfies-aux (m w f worlds evaling-formula)
  (declare (xargs :well-founded-relation l<
                  :measure (list (acl2-count f) (acl2-count worlds))))
  (if evaling-formula
      (cond ((atom f)
             (pdl-satisfies-symbol m w f))
            ((equal (len f) 2)
             (not (pdl-satisfies-aux m w (second f) worlds t)))
            ((equal (len f) 3)
             (cond ((equal (first f) 'v)
                    (or (pdl-satisfies-aux m w (second f) worlds t)
                        (pdl-satisfies-aux m w (third f) worlds t)))
                   ((equal (first f) 'box)
                    (pdl-satisfies-aux
                     m
                     w
                     (third f)
                     (prog-accessible-worlds m w (second f))
                     nil))))
            (t nil))
    (if (consp worlds)
        (and (pdl-satisfies-aux m (car worlds) f nil t)
             (pdl-satisfies-aux m w f (cdr worlds) nil))
      t)))



(defun pdl-satisfies (m w f)
  (pdl-satisfies-aux m w f nil t))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; PROOFS OF CORRECTNESS OF SEMANTICS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; Propositional semantics - negation and disjunction:


(defthm two-elem-formulas-must-be-negations
  (implies (pdl-formulap f a1 a2)
           (iff (equal (len f) 2)
                (equal (first f) '~))))

(defthm negation-semantics-correct
  (implies (and (pdl-formulap f (get-prop-atoms m) (get-prog-atoms m))
                (equal (first f) '~))
           (equal (pdl-satisfies m w (second f))
                  (not (pdl-satisfies m w f)))))



(defthm disjunction-semantics-correct
  (implies (and (equal (len f) 3)
                (equal (first f) 'v))
           (equal (pdl-satisfies m w f)
                  (or (pdl-satisfies m w (second f))
                      (pdl-satisfies m w (third f))))))


; Now we verify the semantics of programs.



(defthm atomic-prog-value-is-correct
  (implies (symbolp p)
           (equal (pdl-prog-value m p) (cdr (assoc p (get-atomic-programs
                                                      (get-frame m)))))))

; complex programs are right length:

(defthm composition-right-length
  (equal (len (rel-compose r1 r2))
         (len r1)))

(defthm union-right-length
  (equal (len (rel-union r1 r2))
         (len r1)))

; needed to prove star-right-length
(defthm rel-star-with-index-gives-proper-len
  (implies (and (natp i)
                (< i (len r)))
           (equal (len (rel-star-with-index i r))
                  (- (len r) i))))

(defthm star-right-length
  (equal (len (rel-star r)) (len r)))


(defthm rel-union-behaves-like-union
 (implies (and (natp n)
           (< n (len A)))
          (iff (member x (nth n (rel-union A B)))
               (or (member x (nth n A)) (member x (nth n B))))))

(defthm union-prog-value-correct
  (implies (and (equal (len p) 3)
                (equal (first p) 'union)
                (natp w)
                (< w (len (pdl-prog-value m (second p)))))
           (iff (member v (prog-accessible-worlds m w p))
                (or (member v (prog-accessible-worlds m w (second p)))
                    (member v (prog-accessible-worlds m w (third p)))))))




; this is one-half of the correctness of the box semantics. The converse also
; kind of holds (though not quite -- the scope of the universal quantifier over
; v is too big if we just naively take the converse without skolemizing).
(defthm box-semantics-semicorrect
  (implies (and (equal (len f) 3)
                (equal (first f) 'box)
                (natp w)
                (< w (len (pdl-prog-value m (second f)))))
           (implies (pdl-satisfies m w f)
                    (implies (member v (prog-accessible-worlds m w (second f)))
                             (pdl-satisfies m v (third f))))))





;here





;rel-star reflexive.

(defthm rel-star-car-looks-right
 (implies (and (natp i)
               (< i (len R)))
          (equal (car (rel-star-with-index i R))
                 (cons i (transitive-closure i R)))))

(defthm rel-star-caar-val-is-i
 (implies (and (natp i)
               (< i (len R)))
          (equal (caar (rel-star-with-index i R)) i)))


(thm
 (implies (and (natp i)
               (< i (len R)))
          (equal (nthcdr i (rel-star-with-index 0 R))
                 (rel-star-with-index i R)))
 :hints (("Goal"
          :in-theory (disable transitive-closure)
          :induct (rel-star-refl-proof-induct i R))))







(thm
 (implies (and (natp i)
               (< i (len R)))
          (equal (caar (rel-star-with-index i R))
                 (- (len (rel-star-with-index i R))


(defun rel-star-refl-proof-induct2 (i r)
  (if (zp i)
      r
    (rel-star-refl-proof-induct2 (- i 1) r)))

(defthm base
  (implies (and (natp i)
                (< i (len R)))
           (equal (nth 0 (rel-star-with-index 0 R))
                 (cons 0 (transitive-closure 0 R)))))

(defthm ind
  (implies (and (natp i)
                (< (+ 1 i) (len R)))
           (implies
            (equal (nth i (rel-star-with-index 0 R))
                   (cons i (transitive-closure i R)))
            (equal (nth (+ 1 i) (rel-star-with-index 0 R))
                   (cons (+ 1 i) (transitive-closure (+ 1 i) R))))))





(thm
 (implies (and (natp i)
               (< i (len R)))
          (equal (nth i (rel-star-with-index 0 R))
                 (cons i (transitive-closure i R))))
  :hints (("Goal"
          :in-theory (disable transitive-closure)
          :induct (rel-star-with-index i R))))





(thm
 (implies (and (natp i)
               (< i (len R)))
          (equal (caar (nth i (rel-star-with-index 0 R)))
                 i))
 :hints (("Goal"
          :in-theory (disable transitive-closure)
          :induct (rel-star-refl-proof-induct2 i R))))

                 


(defun rel-star-refl-proof-induct (i r)
  (declare (xargs :measure (nfix (- (len r) (nfix i)))))
  (if (< (nfix i) (len r))
      (rel-star-refl-proof-induct (+ 1 (nfix i)) r)
    nil))


(thm
 (implies (and (natp i)
               (< i (len R)))
          (equal (nth i (rel-star-with-index 0 R))
                 (cons i (transitive-closure i R))))
 :hints (("Goal"
          :in-theory (disable transitive-closure)
          :induct (rel-star-refl-proof-induct i R))))



          :induct (rel-star-with-index i R))))
 


(thm foo
 (implies (and (natp i)
               (< i (len R)))
          (equal (nth 0 (rel-star-with-index 0 R))
                 (cons 0 (transitive-closure 0 R)))))


(thm
 (member


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


(defun rel-star-with-index (i r)
  (declare (xargs :measure (nfix (- (len r) (nfix i)))))
  (if (< (nfix i) (len r))
      (cons (cons i (transitive-closure i r))
            (rel-star-with-index (+ 1 (nfix i)) r))
    nil))

; takes a list of lists of ints, returns its reflexive transitive closure.
(defun rel-star (r)
  (rel-star-with-index 0 r))









; So everything below here can be considered garbage.



(defun pdl-satisfies-aux-tmp (m w f worlds evaling-formula)
  (declare (xargs :well-founded-relation l<
                  :measure (list (acl2-count f) (acl2-count worlds))))
  (if evaling-formula
      (cond ((atom f)
             (pdl-satisfies-symbol m w f))
            ((equal (len f) 2)
             (not (pdl-satisfies-aux-tmp m w (second f) worlds t)))
            ((equal (len f) 3)
             (cond ((equal (first f) 'v)
                    (or (pdl-satisfies-aux-tmp m w (second f) worlds t)
                        (pdl-satisfies-aux-tmp m w (third f) worlds t)))
                   ((equal (first f) 'diamond)
                    (pdl-satisfies-aux-tmp
                     m
                     w
                     (third f)
                     (prog-accessible-worlds m w (second f))
                     nil))))
            (t nil))
    (if (consp worlds)
        (if (pdl-satisfies-aux-tmp m (car worlds) f nil t)
            t
          (pdl-satisfies-aux-tmp m w f (cdr worlds) nil))
      nil)))

;kbp best formulation (still bad! would work for diamond.)
(defthm box-semantics-correct-r-to-l-diamond
  (let ((ws (prog-accessible-worlds m w (second f))))
    (implies (and (equal (len f) 3)
                  (equal (first f) 'diamond)
                  (natp w)
                  (< w (len (pdl-prog-value m (second f))))
                  (natp i)
                  (< i (len ws)))
             (implies (pdl-satisfies-aux-tmp m (nth i ws) (third f) nil t)
                      (pdl-satisfies-aux-tmp m w f nil t)))))




           (implies (implies (member v (prog-accessible-worlds m w (second f)))
                             (pdl-satisfies m v (third f)))
                    (pdl-satisfies m w f))))







(defun-sk box-semantics-correct-r-l-sk (m w f worlds) 
  (forall x (implies (member x worlds)
                     (pdl-satisfies m w f))))

(in-theory (disable box-semantics-correct-r-l-sk 
                    box-semantics-correct-r-l-sk-necc))

(defthm box-semantics-correct-r-to-l
  (implies (and (equal (len f) 3)
                (equal (first f) 'box)
                (natp w)
                (< w (len (pdl-prog-value m (second f)))))
           (let ((ws (prog-accessible-worlds m w (second f))))
             (implies (box-semantics-correct-r-l-sk m w (third f) ws)
                      (pdl-satisfies m w f))))
  :hints (("Goal"
           :use ((:instance box-semantics-correct-r-l-sk-necc
                            (x (box-semantics-correct-r-l-sk-witness
                                m
                                w
                                (third f)
                                ws)))))))



           (implies (implies (member v (prog-accessible-worlds m w (second f)))
                             (pdl-satisfies m v (third f)))
                    (pdl-satisfies m w f))))



(defthm box-semantics-correct-r-to-l-something
  (implies (and (equal (len f) 3)
                (equal (first f) 'box)
                (natp w)
                (< w (len (pdl-prog-value m (second f)))))
           (let ((ws (prog-accessible-worlds m w (second f))))
             (implies (pdl-satisfies m v (third f))
                      (or (not (member v ws))
                          (pdl-satisfies m w f))))))








(defthm box-semantics-correct-r-to-l
  (implies (and (equal (len f) 3)
                (equal (first f) 'box)
                (natp w)
                (< w (len (pdl-prog-value m (second f)))))
           (implies (implies (member v (prog-accessible-worlds m w (second f)))
                             (pdl-satisfies m v (third f)))
                    (pdl-satisfies m w f))))

  :hints (("Goal"
           :in-theory (disable prog-accessible-worlds))))

;proves, but gets us nothing really
(defthm box-semantics-correct-r-to-l-a
  (implies (and (equal (len f) 3)
                (equal (first f) 'box)
                (natp w)
                (< w (len (pdl-prog-value m (second f)))))
           (let ((ws (prog-accessible-worlds m w (second f))))
             (implies (and (pdl-satisfies-aux m (car ws) (third f) nil t)
                           (pdl-satisfies-aux m w (third f) (cdr ws) nil))
                      (pdl-satisfies m w f)))))

;proves!
(defthm box-semantics-correct-r-to-l-b
  (implies (and (equal (len f) 3)
                (equal (first f) 'box)
                (natp w)
                (< w (len (pdl-prog-value m (second f)))))
           (let ((ws (prog-accessible-worlds m w (second f))))
             (implies (and (pdl-satisfies-aux m (car ws) (third f) nil t)
                           (pdl-satisfies-aux m w (third f) (cdr ws) nil))
                      (implies (member v ws)
                               (pdl-satisfies-aux m v (third f) nil t))))))

(defun foo (A) (if A t nil))

(defthm foolemma1
 (implies (not (consp A)) (not (foo (car A)))))

(thm
 (implies (implies (member a B) (foo a))
          (foo (car B))))

;converse to b pt 1
(defthm box-semantics-correct-r-to-l-c-i
  (implies (and (equal (len f) 3)
                (equal (first f) 'box)
                (natp w)
                (< w (len (pdl-prog-value m (second f)))))
;           (let ((ws (prog-accessible-worlds m w (second f))))
             (implies (implies (member v ws)
                               (pdl-satisfies-aux m v (third f) nil t))
                      (pdl-satisfies-aux m (car ws) (third f) nil t))))
;)

;converse to b pt 2
(defthm box-semantics-correct-r-to-l-c-ii
  (implies (and (equal (len f) 3)
                (equal (first f) 'box)
                (natp w)
                (< w (len (pdl-prog-value m (second f)))))
           (let ((ws (prog-accessible-worlds m w (second f))))
             (implies (implies (member v ws)
                               (pdl-satisfies-aux m v (third f) nil t))
                      (pdl-satisfies-aux m w (third f) (cdr ws) nil)))))


;                      (pdl-satisfies-aux m w f nil t)))))






(defun pdl-satisfies-aux (m w f worlds evaling-formula)
  (declare (xargs :well-founded-relation l<
                  :measure (list (acl2-count f) (acl2-count worlds))))
  (if evaling-formula
      (cond ((atom f)
             (pdl-satisfies-symbol m w f))
            ((equal (len f) 2)
             (not (pdl-satisfies-aux m w (second f) worlds t)))
            ((equal (len f) 3)
             (cond ((equal (first f) 'v)
                    (or (pdl-satisfies-aux m w (second f) worlds t)
                        (pdl-satisfies-aux m w (third f) worlds t)))
                   ((equal (first f) 'diamond)
                    (pdl-satisfies-aux
                     m
                     w
                     (third f)
                     (prog-accessible-worlds m w (second f))
                     nil))))
            (t nil))
    (if (consp worlds)
        (and (pdl-satisfies-aux m (car worlds) f nil t)
             (pdl-satisfies-aux m w f (cdr worlds) nil))
      t)))



(defun pdl-satisfies (m w f)
  (pdl-satisfies-aux m w f nil t))





;proves
(defthm box-semantics-correct-r-to-l-lemma1a
 (implies (and (equal (len f) 3)
               (equal (first f) 'box)
               (natp w))
          (implies (pdl-satisfies-aux m w f ws nil)
                   (implies (member v ws)
                            (pdl-satisfies-aux m v f nil t)))))

;total garbage!
(defthm box-semantics-correct-r-to-l-lemma1b
 (implies (and (equal (len f) 3)
               (equal (first f) 'box)
               (natp w)
               (< w (len ws))
               (< v (len ws)))
          (implies 
           (implies (member v ws)
                    (pdl-satisfies-aux m v f nil t))
           (pdl-satisfies-aux m w f ws nil))))








; Diamond semantics.
;
; Now,
;    M,w \models <\pi> \phi
;    iff
;    \exists w' [ wR_{\pi}w' \wedge M,w' \models \phi.
;
; We therefore prove the two statements of the biconditional separately:
;
; diamond-sem-lemma1:
;    \exists w2 [wR{\pi}w2 \wedge M,w2 \models \phi ]
;    \rightarrow
;    M,w \models <\pi> \phi
;
; diamond-sem-lemma2 (lemma1's converse's contrapositive):
;    \forall w2 \neg [wR_{\pi}w2 \wedge M,w2 \models phi]
;    \rightarrow
;    M,w \not\models <\pi> \phi.


;doesn't prove
(defthm diamond-sem-lemma1-kinda
  (implies (and (equal (len f) 3)
                (equal (first f) 'box)
                (pdl-satisfies-aux m 
                                   w 
                                   (third f) 
                                   (prog-accessible-worlds m w (second f))
                                   nil))
           (pdl-satisfies m w f)))

;proves
(defthm diamond-sem-lemma2-kinda
  (implies (and (equal (len f) 3)
                (equal (first f) 'box)
                (pdl-satisfies m w f))
           (pdl-satisfies-aux
            m
            w
            (third f)
            (prog-accessible-worlds m w (second f))
            nil)))

;doesn't prove
(defthm diamond-sem-kinda
  (implies (and (equal (len f) 3)
                (equal (first f) 'box))
           (equal (pdl-satisfies m w f)
                  (pdl-satisfies-aux m
                                     w
                                     (third f)
                                     (prog-accessible-worlds m w (second f))
                                     nil))))



;correctness of union semantics





(thm
 (implies (and (equal (len p) 3)
               (equal (first p) 'union)
               (natp w)
               (< w (len (pdl-prog-value m (second p)))))
          (implies (pdl-satisfies m w (list 'diamond p f))
                   (or (pdl-satisfies m w (list 'diamond (second p) f))
                       (pdl-satisfies m w (list 'diamond (third p) f))))))


;proves; so where does this get us?
;NB this is exactly "diamond-sem-kinda"
(thm
 (implies (and (equal (len f) 3)
               (equal (first f) 'diamond))
          (iff (pdl-satisfies m w f)
               (pdl-satisfies-aux m 
                                  w 
                                  (third f) 
                                  (prog-accessible-worlds m w (second f))
                                  nil))))


(thm
 (implies (and (equal (len f) 3)
               (equal (first f) 'diamond))
          (implies (pdl-satisfies-aux m
                                      w
                                      (third f)
                                      (prog-accessible-worlds m w (second f))
                                      nil)
                   (and (pdl-satisfies-aux m v (third f) nil t)
                        (member v (prog-accessible-worlds m w (second f)))))))



                
;star prog is reflexive


(defthm indiv-elems-of-rel-star-look-correct
 (implies (and (natp i)
               (< i (len R)))
          (member (cons i (transitive-closure i R))
                  (rel-star-with-index i R))))






(defun foo (i r)
  (declare (xargs :measure (nfix (- (len r) (nfix i)))))
  (if (< (nfix i) (len r))
      (cons i
            (foo (+ 1 (nfix i)) r))
    nil))


(defthm foolemma1
  (implies (and (natp i)
                (< i (len R)))
           (consp (foo i R))))

(defun foolemma4-induction (i r)
  (if (zp i)
      r
    (foolemma4-induction (- i 1) r)))

(defthm foolemma4
  (implies (and (natp i)
                (< i (len R)))
           (equal (nth i (foo 0 R)) i))
  :hints (("Goal"
           :induct (foolemma4-induction i R))))





;proves
(defthm foolemma3
 (implies (and (natp i)
               (< i (len R)))
          (equal (car (foo i R)) 
                 i)))


(defthm foolemma2
 (implies (and (natp i)
               (< i (len R)))
          (equal (nth 0 (foo 0 R)) 0)))

;kindahere


(defthm foolemma2-5
 (implies (and (natp i)
               (< 1 (len R)))
          (equal (nth 1 (foo 0 R)) 1)))







(thm
 (implies (and (natp i)
               (< i (len R)))
          (equal (nth i (foo 0 R)) i))
 :hints (("Goal"
          :induct (foo i R))))



(thm
 (implies (and (natp i)
               (< i (len R)))
          (equal (nth i (rel-star-with-index i R))
                 (cons i (transitive-closure i R)))))

          



          (equal (nth i (rel-star-with-index i R))
                 (cons i (transitive-closure i R))))
 :hints (("Goal"
          :in-theory (disable transitive-closure)
          :induct (rel-star-with-index i R))))



          (member i (nth i (rel-star-with-index i R))))


(thm
 (implies (and (natp i)
               (< i (len R)))
          (member i (nth i (rel-star-with-index i R))))
 :hints (("Goal" :induct (rel-star-with-index i R))))


(defun rel-star-with-index (i r)
  (declare (xargs :measure (nfix (- (len r) (nfix i)))))
  (if (< (nfix i) (len r))
      (cons (cons i (transitive-closure i r))
            (rel-star-with-index (+ 1 (nfix i)) r))
    nil))

(defun one-incr (i li)
  (if (< i (len li))
      (one-incr (+ 1 i) li)
    i))

(thm
 (implies (and (natp i)
               (< i (len R)))
          (member i (rel-star-with-index i R))))

(thm
 (implies (and (natp w)
               (< w (len A)))
          (member w (nth w (rel-star A)))))


(thm
 (implies (and (equal (len p) 2)
;               (natp w)
);               (< w (len (pdl-prog-value m (second p)))))
          (member w (prog-accessible-worlds m w p))))


;star prog is transitive

;actual diamond semantics
(thm
 (implies (and (natp w)
               (pdl-programp p (get-prog-atoms m))
               (< w (len (pdl-prog-value m p)))
               (member v (prog-accessible-worlds m w p))
               (pdl-satisfies m w (list 'diamond p f)))
          (pdl-satisfies m v f)))

(defthm union-semantics-correct
  (implies (and (equal (len p) 3)
                (equal (first p) 'union)
                (natp w)
                (< w (len (pdl-prog-value m (second p)))))
           (iff (pdl-satisfies m w (list 'diamond p f))
                (or (pdl-satisfies m w (list 'diamond (second p) f))
                    (pdl-satisfies m w (list 'diamond (third p) f))))))


;(defun composition-of-single-rel (rel r2)
;  (if (consp rel)
;      (append (nth (car rel) r2)
;            (composition-of-single-rel (cdr rel) r2))
;    nil))
;
;(defun rel-compose (r1 r2)
;  (if (consp r1)
;      (cons (composition-of-single-rel (car r1) r2)
;            (rel-compose (cdr r1) r2))
;    nil))




(defthm composition-prog-value-correct
 (implies (and (equal (len p) 3)
               (equal (first p) 'compose)
               (member w2 (nth w1 (pdl-prog-value m (second p))))
               (member w3 (nth w2 (pdl-prog-value m (third p)))))
          (member w3 (nth w1 (pdl-prog-value m p)))))


(defthm composition-prog-value-correct
 (implies (and (equal (len p) 3)
               (equal (first p) 'compose)
               (member w2 (prog-accessible-worlds m w1 (second p)))
               (member w3 (prog-accessible-worlds m w2 (third p))))
          (member w3 (prog-accessible-worlds m w1 p))))



(defthm composition-correct1
  (let* ((first (first f))
        (second (second f))
        (third (third f))
        (sec-first (first second))
        (sec-second (second second))
        (sec-third (third second)))
    (implies (and (equal (len f) 3)
                  (equal first 'diamond)
                  (equal sec-first 'compose))
             (implies (pdl-satisfies m w f)
                      (pdl-satisfies m w (list 'diamond sec-second
                                             (list 'diamond sec-third
                                                   third)))))))



(defthm star-prog-value-is-correct
  (implies (and (equal (len p) 2)
                (< i (get-num-nodes (get-frame m))))
           (equal (nth i (pdl-prog-value m p))
                  (cons i (transitive-closure i (pdl-prog-value m (second p)))))))
           



(defun-sk diamond-sk (m w1 f)
  (exists w (and (member w (prog-accessible-worlds m w1 (second f)))
                 (pdl-satisfies m w (third f)))))

(in-theory (disable diamond-sk diamond-sk-suff))


; should be iff or equal...
(defthm diamond-semantics-weakly-correct
  (implies (and (equal (len f) 3)
                (equal (first f) 'diamond))
           (implies (pdl-satisfies m w f)
                    (diamond-sk m w f)))
  :hints (("Goal" :use ((:instance diamond-sk-suff (m m) (w1 w) (f f))))))


(defthm diamond-semantics-correct
  (implies (and (equal (len f) 3)
                (equal (first f) 'diamond))
           (iff (pdl-satisfies m w f)
                (prog-accessible-worlds m w (second f)))))
              




