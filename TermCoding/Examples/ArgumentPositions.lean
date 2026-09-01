import TermCoding.LabelledGame

namespace TermCoding.Examples.ArgumentPositions

inductive Var where
  | x | y | z

inductive Symbol where
  | f

def signature : Signature where
  Symbol := Symbol
  arity := fun _ => 3

/-- The equation `f(x,x,y)=z`; positions zero and one deliberately carry the
same variable. -/
def repeatedEquation : Equation signature Var where
  symbol := .f
  args := fun p => if p.val < 2 then .x else .y
  output := .z

/-- Regression theorem: evaluation repeats `a x` in both of the first two
positions. This is the interface that a neighbour-set-only encoding can lose. -/
theorem repeatedEquation_holds_iff {A : Type} (I : Interpretation signature A)
    (a : Assignment Var A) :
    repeatedEquation.Holds I a ↔
      I .f (fun p => if p.val < 2 then a .x else a .y) = a .z := by
  change
    (I .f (fun p => a (if p.val < 2 then .x else .y)) = a .z) ↔
      I .f (fun p => if p.val < 2 then a .x else a .y) = a .z
  have hargs :
      (fun p : Fin 3 => a (if p.val < 2 then .x else .y)) =
        (fun p : Fin 3 => if p.val < 2 then a .x else a .y) := by
    funext p
    by_cases hp : p.val < 2 <;> simp [hp]
  have hI := congrArg (I .f) hargs
  constructor
  · intro h
    exact hI.symm.trans h
  · intro h
    exact hI.trans h

end TermCoding.Examples.ArgumentPositions
