import TermCoding.Dispersion.Spectrum
import TermCoding.Dispersion.Experiments
import TermCoding.Dispersion.ExperimentsSigmaThree

/-!
# Exact least-alphabet results (V10, `prop:small-spectra`)

The two-variable tuples
`τ(x,y) = (f(f(x,y),f(x,x)), f(x,x))` and
`σ(x,y) = (f(x,y), f(f(x,x),f(y,y)))` have least perfect alphabet sizes
`3` and `4` respectively, and consequently `{3^m} ⊆ Spec(τ)` and
`{4^m} ⊆ Spec(σ)`.

The kernel-checked ingredients are in `Experiments.lean` (all `2^4` tables
at size `2`, the explicit witnesses at sizes `3` and `4`) and
`ExperimentsSigmaThree.lean` (all `3^9` tables at size `3`); this file
assembles them into the spectrum statements of `prop:small-spectra`.
-/

namespace TermCoding

namespace Dispersion

/-- No interpretation whatsoever on a three-element alphabet makes `σ`
bijective (all `3^9` binary tables are kernel-checked in
`ExperimentsSigmaThree.lean`). -/
theorem sigma_no_interpretation_three (I : Interpretation diamondSignature (Fin 3)) :
    ¬ Function.Bijective (termMap sigmaPair I) := by
  rw [diamondInterp_surjective I]
  intro h
  exact sigma_no_witness_three ⟨_, h⟩

/-! ### The `τ` spectrum: least element `3` -/

theorem two_notMem_perfectSpectrum_tau : 2 ∉ perfectSpectrum tauPair := by
  rw [mem_perfectSpectrum_square_iff tauPair (by omega)]
  rintro ⟨I, hI⟩
  exact tau_no_interpretation_two I hI

theorem three_mem_perfectSpectrum_tau : 3 ∈ perfectSpectrum tauPair := by
  rw [mem_perfectSpectrum_square_iff tauPair (by omega)]
  exact ⟨diamondInterp addMod3, tau_witness_three⟩

/-- `prop:small-spectra`, first claim: the least element of
`Spec(τ)` is `3`. -/
theorem perfectSpectrum_tau_least :
    3 ∈ perfectSpectrum tauPair ∧
      ∀ n ∈ perfectSpectrum tauPair, 3 ≤ n := by
  refine ⟨three_mem_perfectSpectrum_tau, ?_⟩
  intro n hn
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · exfalso
    have h2 : 2 ≤ n := hn.1
    have : n = 2 := by omega
    rw [this] at hn
    exact two_notMem_perfectSpectrum_tau hn
  · exact h3

/-- `prop:small-spectra`: `{3^m : m ≥ 1} ⊆ Spec(τ)`. -/
theorem pow_three_mem_perfectSpectrum_tau {m : ℕ} (hm : 1 ≤ m) :
    3 ^ m ∈ perfectSpectrum tauPair :=
  pow_mem_perfectSpectrum three_mem_perfectSpectrum_tau hm

/-! ### The `σ` spectrum: least element `4` -/

theorem two_notMem_perfectSpectrum_sigma : 2 ∉ perfectSpectrum sigmaPair := by
  rw [mem_perfectSpectrum_square_iff sigmaPair (by omega)]
  rintro ⟨I, hI⟩
  exact sigma_no_interpretation_two I hI

theorem three_notMem_perfectSpectrum_sigma : 3 ∉ perfectSpectrum sigmaPair := by
  rw [mem_perfectSpectrum_square_iff sigmaPair (by omega)]
  rintro ⟨I, hI⟩
  exact sigma_no_interpretation_three I hI

theorem four_mem_perfectSpectrum_sigma : 4 ∈ perfectSpectrum sigmaPair := by
  rw [mem_perfectSpectrum_square_iff sigmaPair (by omega)]
  exact ⟨diamondInterp sigmaTable, sigma_witness_four⟩

/-- `prop:small-spectra`, second claim: the least element of
`Spec(σ)` is `4`. -/
theorem perfectSpectrum_sigma_least :
    4 ∈ perfectSpectrum sigmaPair ∧
      ∀ n ∈ perfectSpectrum sigmaPair, 4 ≤ n := by
  refine ⟨four_mem_perfectSpectrum_sigma, ?_⟩
  intro n hn
  rcases Nat.lt_or_ge n 4 with h4 | h4
  · exfalso
    have h2 : 2 ≤ n := hn.1
    have h23 : n = 2 ∨ n = 3 := by omega
    rcases h23 with h | h <;> rw [h] at hn
    · exact two_notMem_perfectSpectrum_sigma hn
    · exact three_notMem_perfectSpectrum_sigma hn
  · exact h4

/-- `prop:small-spectra`: `{4^m : m ≥ 1} ⊆ Spec(σ)`. -/
theorem pow_four_mem_perfectSpectrum_sigma {m : ℕ} (hm : 1 ≤ m) :
    4 ^ m ∈ perfectSpectrum sigmaPair :=
  pow_mem_perfectSpectrum four_mem_perfectSpectrum_sigma hm

end Dispersion

end TermCoding
