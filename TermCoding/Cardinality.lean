import Mathlib
import TermCoding.Product

namespace TermCoding

universe uSym uVar uAlpha uBeta

namespace TypeEquiv

/-- Convert the dependency-light equivalence used by the semantic kernel to
Mathlib's `Equiv` once cardinality lemmas are needed. -/
def toEquiv {α : Type uAlpha} {β : Type uBeta} (e : TypeEquiv α β) : α ≃ β where
  toFun := e.toFun
  invFun := e.invFun
  left_inv := e.left_inv
  right_inv := e.right_inv

end TypeEquiv

namespace TermSystem

/-- The number of solutions for one fixed interpretation. -/
noncomputable def solutionCount {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m)
    (I : Interpretation σ A) : Nat :=
  Nat.card (Solutions Γ I)

/-- The number of winning assignments for a fixed occurrence strategy. -/
noncomputable def winningCount {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m)
    (g : OccurrenceStrategy (A := A) Γ) : Nat :=
  Nat.card {a : Assignment Var A // Wins Γ g a}

/-- Mathlib's noncomputable finite enumeration of the strategy type. Its
existence follows from finiteness of the alphabet and the finite occurrence
and argument-position indices. -/
noncomputable instance occurrenceStrategyFintype
    {σ : Signature.{uSym}} {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    [Fintype A] (Γ : TermSystem σ Var m) :
    Fintype (OccurrenceStrategy (A := A) Γ) :=
  Fintype.ofFinite _

/-- A finite enumeration of interpretations when both the signature and the
alphabet are finite. -/
noncomputable instance interpretationFintype
    {σ : Signature.{uSym}} {A : Type uAlpha}
    [Fintype σ.Symbol] [Fintype A] : Fintype (Interpretation σ A) :=
  Fintype.ofFinite _

/-- Exact multiplicativity of the number of winning configurations for a
coordinatewise product of two fixed strategies. -/
theorem winningCount_product {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {B : Type uBeta} {m : Nat}
    (Γ : TermSystem σ Var m) (gA : OccurrenceStrategy (A := A) Γ)
    (gB : OccurrenceStrategy (A := B) Γ) :
    winningCount Γ (productStrategy Γ gA gB) =
      winningCount Γ gA * winningCount Γ gB := by
  rw [winningCount, winningCount, winningCount]
  rw [Nat.card_congr (winningProductEquiv Γ gA gB).toEquiv]
  exact Nat.card_prod _ _

/-- The finite maximum number of winning assignments over all occurrence
strategies on a fixed alphabet type. -/
noncomputable def winningMax {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} [Fintype Var] [Fintype A]
    (Γ : TermSystem σ Var m) : Nat :=
  (Finset.univ : Finset (OccurrenceStrategy (A := A) Γ)).sup
    (winningCount Γ)

/-- The finite maximum solution count over all interpretations of the
original signature. -/
noncomputable def maxSolutionCount {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    [Fintype σ.Symbol] [Fintype Var] [Fintype A]
    (Γ : TermSystem σ Var m) : Nat :=
  (Finset.univ : Finset (Interpretation σ A)).sup (solutionCount Γ)

/-- Every fixed strategy is bounded by the finite maximum. -/
theorem winningCount_le_winningMax {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    [Fintype Var] [Fintype A] (Γ : TermSystem σ Var m)
    (g : OccurrenceStrategy (A := A) Γ) :
    winningCount Γ g ≤ winningMax (A := A) Γ := by
  classical
  exact Finset.le_sup (s := Finset.univ) (f := winningCount Γ)
    (Finset.mem_univ g)

/-- On a nonempty finite alphabet, some strategy attains the finite maximum. -/
theorem exists_winningCount_eq_winningMax {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    [Fintype Var] [Fintype A] [Nonempty A]
    (Γ : TermSystem σ Var m) :
    ∃ g : OccurrenceStrategy (A := A) Γ,
      winningCount Γ g = winningMax (A := A) Γ := by
  classical
  obtain ⟨g, _, hg⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (OccurrenceStrategy (A := A) Γ))
    Finset.univ_nonempty (winningCount Γ)
  exact ⟨g, hg.symm⟩

/-- Finite product lower bound for the optimal winning count. This is the
cardinal maximisation form of the paper's product construction. -/
theorem winningMax_mul_le_product {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {B : Type uBeta} {m : Nat}
    [Fintype Var] [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (Γ : TermSystem σ Var m) :
    winningMax (A := A) Γ * winningMax (A := B) Γ ≤
      winningMax (A := A × B) Γ := by
  obtain ⟨gA, hgA⟩ := exists_winningCount_eq_winningMax (A := A) Γ
  obtain ⟨gB, hgB⟩ := exists_winningCount_eq_winningMax (A := B) Γ
  rw [← hgA, ← hgB, ← winningCount_product]
  exact winningCount_le_winningMax Γ (productStrategy Γ gA gB)

/-- Diversification with the inherited interpretation preserves the exact
number of solutions for every finite alphabet and finite variable type. -/
theorem solutionCard_diversify_inherited {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (I : Interpretation σ A) :
    Nat.card (Solutions Γ I) =
      Nat.card (Solutions (diversify Γ) (diversifyInterpretation Γ I)) := by
  exact Nat.card_congr (solutionsEquivDiversify Γ I).toEquiv

/-- The labelled-game bridge preserves the exact number of configurations
for every fixed diversified strategy. -/
theorem winningCard_eq_diversifiedSolutionCard {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (g : OccurrenceStrategy (A := A) Γ) :
    Nat.card {a : Assignment Var A // Wins Γ g a} =
      Nat.card (Solutions (diversify Γ) (strategyToInterpretation Γ g)) := by
  exact Nat.card_congr (winningEquivDiversifiedSolutions Γ g).toEquiv

/-- A fixed original interpretation has exactly the winning count of its
inherited diversified strategy. -/
theorem solutionCount_eq_inheritedWinningCount {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (I : Interpretation σ A) :
    solutionCount Γ I =
      winningCount Γ
        (interpretationToStrategy Γ (diversifyInterpretation Γ I)) := by
  rw [solutionCount, winningCount]
  calc
    Nat.card (Solutions Γ I) =
        Nat.card (Solutions (diversify Γ) (diversifyInterpretation Γ I)) :=
      solutionCard_diversify_inherited Γ I
    _ = Nat.card
        {a : Assignment Var A //
          Wins Γ (interpretationToStrategy Γ (diversifyInterpretation Γ I)) a} := by
      simpa using
        (winningCard_eq_diversifiedSolutionCard Γ
          (interpretationToStrategy Γ (diversifyInterpretation Γ I))).symm

/-- The upper half of the finite sandwich: diversification and passage to the
labelled game can only increase the optimum. -/
theorem maxSolutionCount_le_winningMax {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    [Fintype σ.Symbol] [Fintype Var] [Fintype A]
    (Γ : TermSystem σ Var m) :
    maxSolutionCount (A := A) Γ ≤ winningMax (A := A) Γ := by
  classical
  apply Finset.sup_le
  intro I _
  rw [solutionCount_eq_inheritedWinningCount]
  exact winningCount_le_winningMax (A := A) Γ _

end TermSystem

end TermCoding
