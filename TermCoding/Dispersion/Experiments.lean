import TermCoding.Dispersion.Basic
import TermCoding.Dispersion.Diamond
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Basic

/-!
# Kernel checks of the `k = 2` experiments (V6, Section 7.1)

V6 reports computational experiments for two square pairs over one binary
symbol `f`:

* `τ(x,y) = (f(f(x,y), f(x,x)), f(x,x))`, "appears to have spectrum
  `{3, 4, 5, …}` (all sizes except `2`)";
* `σ(x,y) = (f(x,y), f(f(x,x), f(y,y)))`, "appears to have no witness on `2`
  or `3` elements but does have a `4`-element witness".

The following small cases are decided by the Lean kernel (`decide`; no
native evaluation; no logical dependencies beyond the standard three):

* `tau_no_witness_two`, `sigma_no_witness_two` -- no interpretation on a
  two-element alphabet is bijective (exhaustive over the `16` binary
  operations);
* `tau_witness_three` -- addition mod `3` is a `3`-element witness for `τ`;
* `sigma_witness_four` -- an explicit `4`-element witness for `σ`, found by
  a backtracking search (`scripts/k2_search.py`).

Not kernel-checked: the absence of a `3`-element witness for `σ` (the search
over `3^9` tables was run only by the script), and the spectrum claims.
-/

namespace TermCoding

namespace Dispersion

/-- `τ(x,y) = (f(f(x,y), f(x,x)), f(x,x))`. -/
def tauPair : Instance diamondSignature 2 2 :=
  ![fapp (fapp (.var 0) (.var 1)) (fapp (.var 0) (.var 0)), fapp (.var 0) (.var 0)]

/-- `σ(x,y) = (f(x,y), f(f(x,x), f(y,y)))`. -/
def sigmaPair : Instance diamondSignature 2 2 :=
  ![fapp (.var 0) (.var 1), fapp (fapp (.var 0) (.var 0)) (fapp (.var 1) (.var 1))]

/-- No binary operation on a two-element set makes `τ` bijective. -/
theorem tau_no_witness_two :
    ¬ ∃ g : Fin 2 → Fin 2 → Fin 2, Function.Bijective (termMap tauPair (diamondInterp g)) := by
  decide

/-- No binary operation on a two-element set makes `σ` bijective. -/
theorem sigma_no_witness_two :
    ¬ ∃ g : Fin 2 → Fin 2 → Fin 2, Function.Bijective (termMap sigmaPair (diamondInterp g)) := by
  decide

/-- Consequently no interpretation whatsoever on `Fin 2` is a `τ`-witness. -/
theorem tau_no_interpretation_two (I : Interpretation diamondSignature (Fin 2)) :
    ¬ Function.Bijective (termMap tauPair I) := by
  rw [diamondInterp_surjective I]
  intro h
  exact tau_no_witness_two ⟨_, h⟩

theorem sigma_no_interpretation_two (I : Interpretation diamondSignature (Fin 2)) :
    ¬ Function.Bijective (termMap sigmaPair I) := by
  rw [diamondInterp_surjective I]
  intro h
  exact sigma_no_witness_two ⟨_, h⟩

/-- Addition mod `3`. -/
def addMod3 : Fin 3 → Fin 3 → Fin 3 := fun x y => x + y

/-- `τ` is bijective on `Fin 3` under addition mod `3`. -/
theorem tau_witness_three : Function.Bijective (termMap tauPair (diamondInterp addMod3)) := by
  decide

/-- The `4`-element table found by `scripts/k2_search.py`
(rows indexed by the first argument). -/
def sigmaTable : Fin 4 → Fin 4 → Fin 4 :=
  ![![2, 2, 3, 2], ![1, 0, 1, 3], ![0, 1, 1, 2], ![3, 0, 0, 3]]

/-- `σ` is bijective on `Fin 4` under `sigmaTable`. -/
theorem sigma_witness_four : Function.Bijective (termMap sigmaPair (diamondInterp sigmaTable)) := by
  decide

/-- `τ` is a `BIJ_2` yes-instance and `σ` is a `BIJ_2` yes-instance
(with witnesses of sizes `3` and `4`). -/
theorem tau_bij : BIJ tauPair :=
  ⟨Fin 3, inferInstance, by simp, diamondInterp addMod3, tau_witness_three⟩

theorem sigma_bij : BIJ sigmaPair :=
  ⟨Fin 4, inferInstance, by simp, diamondInterp sigmaTable, sigma_witness_four⟩

end Dispersion

end TermCoding
