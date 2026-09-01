import TermCoding.Normalisation
import TermCoding.Sandwich

namespace TermCoding

universe uSym uVar uAlpha

namespace TermTheory

/-- Number of solutions of an arbitrary finite term theory for one fixed
interpretation. -/
noncomputable def solutionCount {σ : Signature.{uSym}} {Original : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermTheory σ Original m)
    (I : Interpretation σ A) : Nat :=
  Nat.card (Solutions Γ I)

/-- Maximum solution count of an arbitrary finite term theory over a fixed
finite alphabet type. -/
noncomputable def maxSolutionCount {σ : Signature.{uSym}}
    {Original : Type uVar} {A : Type uAlpha} {m : Nat}
    [Fintype σ.Symbol] [Fintype Original] [Fintype A]
    (Γ : TermTheory σ Original m) : Nat :=
  (Finset.univ : Finset (Interpretation σ A)).sup (solutionCount Γ)

/-- Normalisation preserves the exact solution count for every fixed
interpretation. -/
theorem solutionCount_eq_normalized {σ : Signature.{uSym}}
    {Original : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermTheory σ Original m) (I : Interpretation σ A) :
    solutionCount Γ I =
      TermSystem.solutionCount (Normalisation.system Γ) I := by
  exact Nat.card_congr (Normalisation.solutionsEquiv Γ I).toEquiv

/-- Normalisation preserves the maximum code size on every finite alphabet. -/
theorem maxSolutionCount_eq_normalized {σ : Signature.{uSym}}
    {Original : Type uVar} {A : Type uAlpha} {m : Nat}
    [Fintype σ.Symbol] [Fintype Original] [Fintype A]
    (Γ : TermTheory σ Original m) :
    maxSolutionCount (A := A) Γ =
      TermSystem.maxSolutionCount (A := A) (Normalisation.system Γ) := by
  classical
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro I _
    rw [solutionCount_eq_normalized]
    exact Finset.le_sup (s := Finset.univ)
      (f := TermSystem.solutionCount (Normalisation.system Γ))
      (Finset.mem_univ I)
  · apply Finset.sup_le
    intro I _
    rw [← solutionCount_eq_normalized]
    exact Finset.le_sup (s := Finset.univ) (f := solutionCount Γ)
      (Finset.mem_univ I)

/-- Principal finite theorem for arbitrary term equations. After complete
canonical normalisation, let `k` be the number of quotient variables. For
every `n ≥ k`, the paper's labelled winning maximum sandwiches the original
maximum code size at alphabet size `n`. -/
theorem finiteSandwich {σ : Signature.{uSym}} {Original : Type uVar}
    {n m : Nat} [Fintype σ.Symbol] [Fintype Original] [Nonempty Original]
    (Γ : TermTheory σ Original m)
    (hcard : Normalisation.variableCount Γ ≤ n) :
    TermSystem.winningMax
        (A := Fin (n / Normalisation.variableCount Γ))
        (Normalisation.system Γ) ≤
      maxSolutionCount (A := Fin n) Γ ∧
    maxSolutionCount (A := Fin n) Γ ≤
      TermSystem.winningMax (A := Fin n) (Normalisation.system Γ) := by
  have hs := TermSystem.finiteSandwich_fintype
    (Var := Normalisation.Variable Γ) hcard
    (Normalisation.system Γ) (Normalisation.system_noCollision Γ)
  have hn := maxSolutionCount_eq_normalized (A := Fin n) Γ
  constructor
  · rw [hn]
    exact hs.1
  · rw [hn]
    exact hs.2

end TermTheory

end TermCoding
