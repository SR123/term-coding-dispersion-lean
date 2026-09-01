import TermCoding.FullSandwich
import TermCoding.OrdinaryGame

namespace TermCoding

universe uSym uVar

namespace TermTheory

/-- Exact finite ordinary-digraph sandwich for the manuscript's functional
normal-form special case.  The ordinary game is built on the variables and
the union of argument variables of their unique defining equations. -/
theorem finiteSandwich_ordinary_of_outputFunctional
    {σ : Signature.{uSym}} {Original : Type uVar}
    {n m : Nat} [Fintype σ.Symbol] [Fintype Original]
    [Nonempty Original] (Γ : TermTheory σ Original m)
    (hcard : Normalisation.variableCount Γ ≤ n)
    (hfun : TermSystem.OutputFunctional (Normalisation.system Γ)) :
    TermSystem.ordinaryWinningMax
        (A := Fin (n / Normalisation.variableCount Γ))
        (Normalisation.system Γ) ≤
      maxSolutionCount (A := Fin n) Γ ∧
    maxSolutionCount (A := Fin n) Γ ≤
      TermSystem.ordinaryWinningMax
        (A := Fin n) (Normalisation.system Γ) := by
  have hs := finiteSandwich Γ hcard
  constructor
  · rw [←
      TermSystem.winningMax_eq_ordinaryWinningMax_of_outputFunctional
        (A := Fin (n / Normalisation.variableCount Γ))
        (Normalisation.system Γ) hfun]
    exact hs.1
  · rw [←
      TermSystem.winningMax_eq_ordinaryWinningMax_of_outputFunctional
        (A := Fin n) (Normalisation.system Γ) hfun]
    exact hs.2

end TermTheory

end TermCoding
