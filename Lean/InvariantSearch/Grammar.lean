import Veil

inductive Const (X : Type) where
| qvar : String → Const X
| indiv : X → Const X

inductive Pred (X : Type) (R : Type) where
| eq : Const X → Const X → Pred X R
| neq : Const X → Const X → Pred X R
| rel : R → List (Const X) → Pred X R
| neg : Pred X R → Pred X R

inductive Conj (X R : Type) where
| conj : Pred X R → Conj X R → Conj X R
| T : Conj X R

inductive Disj (X R : Type) where
| disj : Pred X R → Disj X R → Disj X R
| single : Pred X R → Disj X R

inductive Candidate (X R : Type) where
| cand : Conj X R → Disj X R → Candidate X R
