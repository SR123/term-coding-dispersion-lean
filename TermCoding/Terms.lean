import TermCoding.Syntax

namespace TermCoding

universe uSym uVar uAlpha

/-- A first-order term over an arity-indexed signature. Argument order and
repetitions are retained by the finite position map. -/
inductive Term (σ : Signature.{uSym}) (Var : Type uVar) where
  | var (v : Var)
  | app (symbol : σ.Symbol)
      (args : Fin (σ.arity symbol) → Term σ Var)

namespace Term

/-- Evaluation of a term under an interpretation and variable assignment. -/
def eval {σ : Signature.{uSym}} {Var : Type uVar} {A : Type uAlpha}
    (I : Interpretation σ A) (a : Assignment Var A) : Term σ Var → A
  | .var v => a v
  | .app s args => I s (fun p => eval I a (args p))

end Term

/-- One equation between arbitrary first-order terms. -/
structure TermEquation (σ : Signature.{uSym}) (Var : Type uVar) where
  lhs : Term σ Var
  rhs : Term σ Var

/-- A finite family of arbitrary term equations. -/
abbrev TermTheory (σ : Signature.{uSym}) (Var : Type uVar) (m : Nat) :=
  Fin m → TermEquation σ Var

namespace TermEquation

/-- Satisfaction of one arbitrary term equation. -/
def Holds {σ : Signature.{uSym}} {Var : Type uVar} {A : Type uAlpha}
    (e : TermEquation σ Var) (I : Interpretation σ A)
    (a : Assignment Var A) : Prop :=
  e.lhs.eval I a = e.rhs.eval I a

end TermEquation

namespace TermTheory

/-- Satisfaction of a finite family of arbitrary term equations. -/
def Holds {σ : Signature.{uSym}} {Var : Type uVar} {A : Type uAlpha}
    {m : Nat} (Γ : TermTheory σ Var m) (I : Interpretation σ A)
    (a : Assignment Var A) : Prop :=
  ∀ i, (Γ i).Holds I a

/-- Satisfying assignments for an arbitrary term theory and fixed
interpretation. -/
def Solutions {σ : Signature.{uSym}} {Var : Type uVar} {A : Type uAlpha}
    {m : Nat} (Γ : TermTheory σ Var m) (I : Interpretation σ A) :=
  {a : Assignment Var A // Γ.Holds I a}

end TermTheory

end TermCoding
