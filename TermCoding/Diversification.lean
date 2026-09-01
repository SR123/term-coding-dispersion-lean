import TermCoding.Syntax

namespace TermCoding

universe uSym uVar uAlpha

namespace TermSystem

/-- The diversified signature has one fresh symbol for each equation
occurrence. Its arity is inherited from the symbol in that occurrence. -/
def diversifiedSignature {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}
    (Γ : TermSystem σ Var m) : Signature where
  Symbol := Fin m
  arity := fun i => σ.arity (Γ i).symbol

/-- Replace the symbol in every equation by its own occurrence index. -/
def diversify {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}
    (Γ : TermSystem σ Var m) : TermSystem (diversifiedSignature Γ) Var m :=
  fun i => {
    symbol := i
    args := (Γ i).args
    output := (Γ i).output
  }

@[simp] theorem diversify_args {σ : Signature.{uSym}} {Var : Type uVar}
    {m : Nat} (Γ : TermSystem σ Var m) (i : Fin m) :
    ((diversify Γ) i).args = (Γ i).args := by
  rfl

@[simp] theorem diversify_output {σ : Signature.{uSym}} {Var : Type uVar}
    {m : Nat} (Γ : TermSystem σ Var m) (i : Fin m) :
    ((diversify Γ) i).output = (Γ i).output := by
  rfl

@[simp] theorem diversified_arity {σ : Signature.{uSym}} {Var : Type uVar}
    {m : Nat} (Γ : TermSystem σ Var m) (i : Fin m) :
    (diversifiedSignature Γ).arity i = σ.arity (Γ i).symbol := by
  rfl

/-- Every original interpretation induces a diversified interpretation by
using the parent operation at each occurrence. -/
def diversifyInterpretation {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m)
    (I : Interpretation σ A) : Interpretation (diversifiedSignature Γ) A :=
  fun i => I (Γ i).symbol

/-- Reusing the parent operation at every occurrence preserves satisfaction
exactly. -/
theorem holds_diversify_iff {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m)
    (I : Interpretation σ A) (a : Assignment Var A) :
    (diversify Γ).Holds (diversifyInterpretation Γ I) a ↔ Γ.Holds I a := by
  rfl

/-- The preceding logical equivalence is an actual equivalence of solution
types for each fixed interpretation. -/
def solutionsEquivDiversify {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m)
    (I : Interpretation σ A) :
    TypeEquiv (Solutions Γ I)
      (Solutions (diversify Γ) (diversifyInterpretation Γ I)) where
  toFun a := ⟨a.1, (holds_diversify_iff Γ I a.1).2 a.2⟩
  invFun a := ⟨a.1, (holds_diversify_iff Γ I a.1).1 a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end TermSystem

end TermCoding
