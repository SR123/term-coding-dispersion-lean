import TermCoding.Diversification

namespace TermCoding

universe uSym uVar uAlpha

namespace TermSystem

/-- A local strategy assigns one rule to every equation occurrence. The rule
sees the ordered argument positions, so repeated and reordered variables are
handled without loss of information. -/
abbrev OccurrenceStrategy {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m) :=
  (i : Fin m) → (Fin (σ.arity (Γ i).symbol) → A) → A

/-- A variable assignment wins when every occurrence rule returns the value
of that occurrence's output variable. -/
def Wins {σ : Signature.{uSym}} {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (g : OccurrenceStrategy (A := A) Γ)
    (a : Assignment Var A) : Prop :=
  ∀ i, g i (fun p => a ((Γ i).args p)) = a (Γ i).output

/-- A diversified interpretation is definitionally an occurrence strategy. -/
def interpretationToStrategy {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m)
    (I : Interpretation (diversifiedSignature Γ) A) : OccurrenceStrategy (A := A) Γ :=
  I

/-- An occurrence strategy is definitionally a diversified interpretation. -/
def strategyToInterpretation {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m)
    (g : OccurrenceStrategy (A := A) Γ) : Interpretation (diversifiedSignature Γ) A :=
  g

/-- The exact semantic bridge used by the labelled guessing-game theorem. -/
theorem holds_diversified_iff_wins {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m)
    (I : Interpretation (diversifiedSignature Γ) A) (a : Assignment Var A) :
    (diversify Γ).Holds I a ↔ Wins Γ (interpretationToStrategy Γ I) a := by
  rfl

/-- The exact bridge in the reverse direction, starting from a local
strategy. -/
theorem wins_iff_holds_diversified {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m)
    (g : OccurrenceStrategy (A := A) Γ) (a : Assignment Var A) :
    Wins Γ g a ↔ (diversify Γ).Holds (strategyToInterpretation Γ g) a := by
  rfl

/-- Winning configurations and solutions of the corresponding diversified
interpretation are equivalent, not merely equinumerous. -/
def winningEquivDiversifiedSolutions {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m)
    (g : OccurrenceStrategy (A := A) Γ) :
    TypeEquiv {a : Assignment Var A // Wins Γ g a}
      (Solutions (diversify Γ) (strategyToInterpretation Γ g)) where
  toFun a := ⟨a.1, (wins_iff_holds_diversified Γ g a.1).1 a.2⟩
  invFun a := ⟨a.1, (wins_iff_holds_diversified Γ g a.1).2 a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end TermSystem

end TermCoding
