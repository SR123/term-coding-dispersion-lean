import TermCoding.Dispersion.Exponent
import TermCoding.Dispersion.SquareBijectivity
import TermCoding.Dispersion.Reductions
import TermCoding.Dispersion.OneOutput

/-!
# The complexity landscape (V6, `thm:landscape`)

The mathematical parts of `thm:landscape`, assembled from the modules above:

* (i) `landscape_square` -- the square restriction of `Perfect-Disp` is
  exactly `BIJ`;
* (ii) `landscape_reduction` -- for every fixed `r ≥ 3` (and every `k ≥ r`)
  the syntactic reduction `BIJ_3 ≤_m Perfect-Disp_r` with a linear size
  bound; the conditional undecidability transfer is
  `decidable_bij3_of_decidable_perfect`;
* (iii) `landscape_rate` -- perfect dispersion implies full rate, and the
  converse fails (the diamond).

Parts (iv) and (v) (polynomial-time decidability of `Full-Rate-Disp` and of
`Asymp-Threshold`) are complexity statements about an algorithm; their
mathematical content is `fullRate_iff_termCutNumber`,
`threshold_iff_of_lowerBound` and `decideThreshold_correct` in the
conditional layer, and the algorithmic part is external (see the reports).
-/

namespace TermCoding

namespace Dispersion

universe uSym

variable {σ : Signature.{uSym}} [Fintype σ.Symbol]

/-- `thm:landscape` (i). -/
theorem landscape_square {k : Nat} (t : Instance σ k k) : PerfectDisp t ↔ BIJ t :=
  perfectDisp_iff_bij t

/-- `thm:landscape` (ii). -/
def landscape_reduction (k r : Nat) (hr : 3 ≤ r) (hrk : r ≤ k) :
    ManyOneReduction (BIJ (σ := σ) (k := 3)) (PerfectDisp (σ := σ) (k := k) (r := r)) :=
  reduction_nr k r hr hrk

/-- `thm:landscape` (iii). -/
theorem landscape_rate :
    (∀ {k r : Nat} (t : Instance σ k r), 0 < r → PerfectDisp t → FullRateDisp t) ∧
      ∃ t : Instance diamondSignature 4 4, FullRateDisp t ∧ ¬ PerfectDisp t :=
  ⟨fun t hr h => fullRateDisp_of_perfectDisp t hr h, not_perfect_of_fullRate_fails⟩

end Dispersion

end TermCoding
