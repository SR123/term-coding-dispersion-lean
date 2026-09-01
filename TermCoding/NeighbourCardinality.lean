import TermCoding.Cardinality
import TermCoding.NeighbourGame

namespace TermCoding

universe uSym uVar uAlpha

namespace TermSystem

/-- The number of winning assignments for a fixed neighbour strategy. -/
noncomputable def neighbourWinningCount {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (h : NeighbourStrategy (A := A) Γ) : Nat :=
  Nat.card {a : Assignment Var A // NeighbourWins Γ h a}

noncomputable instance neighbourFintype {σ : Signature.{uSym}}
    {Var : Type uVar} {m : Nat} [Fintype Var]
    (Γ : TermSystem σ Var m) (i : Fin m) : Fintype (Neighbour Γ i) :=
  by
    letI : Finite (Neighbour Γ i) :=
      Finite.of_injective Subtype.val Subtype.val_injective
    exact Fintype.ofFinite _

noncomputable instance neighbourStrategyFintype {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    [Fintype Var] [Fintype A] (Γ : TermSystem σ Var m) :
    Fintype (NeighbourStrategy (A := A) Γ) :=
  Fintype.ofFinite _

/-- The finite optimum in the paper's labelled neighbour-variable game. -/
noncomputable def neighbourWinningMax {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    [Fintype Var] [Fintype A] (Γ : TermSystem σ Var m) : Nat :=
  (Finset.univ : Finset (NeighbourStrategy (A := A) Γ)).sup
    (neighbourWinningCount Γ)

theorem winningCount_eq_neighbourCollapse {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (g : OccurrenceStrategy (A := A) Γ) :
    winningCount Γ g =
      neighbourWinningCount Γ (collapseToNeighbourStrategy Γ g) := by
  exact Nat.card_congr (winningEquivNeighbourCollapse Γ g).toEquiv

theorem neighbourWinningCount_eq_expand {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (h : NeighbourStrategy (A := A) Γ) :
    neighbourWinningCount Γ h =
      winningCount Γ (expandNeighbourStrategy Γ h) := by
  exact Nat.card_congr (winningEquivNeighbourExpand Γ h).toEquiv

/-- The position-sensitive optimum and the paper's neighbour-variable
labelled-game optimum are equal. Repetition and argument order therefore do
not create a gap at the level of winning assignments. -/
theorem winningMax_eq_neighbourWinningMax {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    [Fintype Var] [Fintype A] (Γ : TermSystem σ Var m) :
    winningMax (A := A) Γ = neighbourWinningMax (A := A) Γ := by
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro g _
    rw [winningCount_eq_neighbourCollapse]
    exact Finset.le_sup (s := Finset.univ)
      (f := neighbourWinningCount Γ) (Finset.mem_univ _)
  · apply Finset.sup_le
    intro h _
    rw [neighbourWinningCount_eq_expand]
    exact winningCount_le_winningMax Γ _

end TermSystem

end TermCoding
