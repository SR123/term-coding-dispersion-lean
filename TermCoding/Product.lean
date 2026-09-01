import TermCoding.LabelledGame

namespace TermCoding

universe uSym uVar uAlpha uBeta

namespace TermSystem

/-- Project a product-alphabet assignment to its first coordinate. -/
def fstAssignment {Var : Type uVar} {A : Type uAlpha} {B : Type uBeta}
    (a : Assignment Var (A × B)) : Assignment Var A :=
  fun v => (a v).1

/-- Project a product-alphabet assignment to its second coordinate. -/
def sndAssignment {Var : Type uVar} {A : Type uAlpha} {B : Type uBeta}
    (a : Assignment Var (A × B)) : Assignment Var B :=
  fun v => (a v).2

/-- Combine two assignments coordinatewise into a product-alphabet
assignment. -/
def pairAssignment {Var : Type uVar} {A : Type uAlpha} {B : Type uBeta}
    (a : Assignment Var A) (b : Assignment Var B) : Assignment Var (A × B) :=
  fun v => (a v, b v)

/-- The coordinatewise product of two occurrence strategies. This is the
finite product construction behind supermultiplicativity. -/
def productStrategy {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {B : Type uBeta} {m : Nat}
    (Γ : TermSystem σ Var m) (gA : OccurrenceStrategy (A := A) Γ)
    (gB : OccurrenceStrategy (A := B) Γ) :
    OccurrenceStrategy (A := A × B) Γ :=
  fun i input =>
    (gA i (fun p => (input p).1), gB i (fun p => (input p).2))

/-- A configuration wins for the product strategy exactly when each
coordinate projection wins for the corresponding factor strategy. -/
theorem wins_product_iff {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {B : Type uBeta} {m : Nat}
    (Γ : TermSystem σ Var m) (gA : OccurrenceStrategy (A := A) Γ)
    (gB : OccurrenceStrategy (A := B) Γ) (a : Assignment Var (A × B)) :
    Wins Γ (productStrategy Γ gA gB) a ↔
      Wins Γ gA (fstAssignment a) ∧ Wins Γ gB (sndAssignment a) := by
  constructor
  · intro h
    constructor
    · intro i
      exact congrArg Prod.fst (h i)
    · intro i
      exact congrArg Prod.snd (h i)
  · intro h i
    apply Prod.ext
    · exact h.1 i
    · exact h.2 i

/-- The exact type-level form of multiplicativity: winning configurations
for the coordinatewise product strategy are equivalent to pairs of winning
configurations for the two factor strategies. -/
def winningProductEquiv {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {B : Type uBeta} {m : Nat}
    (Γ : TermSystem σ Var m) (gA : OccurrenceStrategy (A := A) Γ)
    (gB : OccurrenceStrategy (A := B) Γ) :
    TypeEquiv
      {a : Assignment Var (A × B) // Wins Γ (productStrategy Γ gA gB) a}
      ({a : Assignment Var A // Wins Γ gA a} ×
        {b : Assignment Var B // Wins Γ gB b}) where
  toFun a :=
    (⟨fstAssignment a.1, (wins_product_iff Γ gA gB a.1).1 a.2 |>.1⟩,
      ⟨sndAssignment a.1, (wins_product_iff Γ gA gB a.1).1 a.2 |>.2⟩)
  invFun ab :=
    ⟨pairAssignment ab.1.1 ab.2.1,
      (wins_product_iff Γ gA gB (pairAssignment ab.1.1 ab.2.1)).2
        ⟨ab.1.2, ab.2.2⟩⟩
  left_inv a := by
    apply Subtype.ext
    funext v
    exact Prod.ext rfl rfl
  right_inv ab := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · apply Subtype.ext
      rfl

end TermSystem

end TermCoding
