import TermCoding.Dispersion.Basic
import TermCoding.Dispersion.SquareBijectivity
import TermCoding.Dispersion.Padding
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin

/-!
# Reductions from square bijectivity to perfect dispersion (V6, Section 6.4)

`padInstance p` is the actual syntax transformer of `thm:reduction-kk` and
`thm:reduction-nr`: from a square instance `p` with `k₀` inputs and
outputs it produces the instance with `k ≥ r ≥ k₀` inputs/outputs
`(p_1(x_1..x_{k₀}), …, p_{k₀}(x_1..x_{k₀}), x_{k₀+1}, …, x_r)`; the inputs
`x_{r+1}, …, x_k` do not occur.

* `termMap_padInstance` -- semantic correctness: `Θ^I` of the padded
  instance is `padMap (Θ^I of p)` for *every* interpretation.
* `perfectDisp_padInstance_iff` -- yes/no preservation:
  `Perfect-Disp_r(padInstance p) ⇔ BIJ_{k₀}(p)`.
* `size_padInstance` -- the exact size identity
  `‖padInstance p‖ + 2 k₀ = ‖p‖ + 2 r`, hence a linear size bound.
* `reduction_kk`, `reduction_nr` -- the packaged many-one reductions
  `BIJ_3 ≤_m Perfect-Disp_k` on square instances (`k ≥ 3`) and
  `BIJ_3 ≤_m Perfect-Disp_r` on the subfamily with `k ≥ r ≥ 3` inputs.

Lean has no cost model; "polynomial time" is documented by the structurally
recursive, computable definition of `padInstance` together with the proved
linear size bound.
-/

namespace TermCoding

namespace Dispersion

universe uSym uAlpha

variable {σ : Signature.{uSym}}

theorem Term.size_mapVar {V W : Type} (f : V → W) :
    ∀ t : Term σ V, (Term.mapVar f t).size = t.size
  | .var _ => rfl
  | .app s args => by
      simp only [Term.mapVar, Term.size]
      congr 1
      exact Finset.sum_congr rfl (fun p _ => Term.size_mapVar f (args p))

/-- The padding transformer. -/
def padInstance {k₀ r k : Nat} (p : Instance σ k₀ k₀) (hk₀r : k₀ ≤ r) (hrk : r ≤ k) :
    Instance σ k r :=
  fun i =>
    if h : i.val < k₀ then (p ⟨i.val, h⟩).mapVar (Fin.castLE (hk₀r.trans hrk))
    else .var (Fin.castLE hrk i)

/-- Semantic correctness of the transformer for every interpretation. -/
theorem termMap_padInstance {A : Type uAlpha} {k₀ r k : Nat} (p : Instance σ k₀ k₀)
    (hk₀r : k₀ ≤ r) (hrk : r ≤ k) (I : Interpretation σ A) :
    termMap (padInstance p hk₀r hrk) I = padMap (termMap p I) hk₀r hrk := by
  funext a i
  simp only [termMap, padInstance, padMap]
  by_cases h : i.val < k₀
  · rw [dif_pos h, dif_pos h, Term.eval_mapVar]
    rfl
  · rw [dif_neg h, dif_neg h]
    rfl

/-- Yes/no preservation: the padded instance is perfectly dispersive on some
finite alphabet iff the original square instance is a `BIJ` yes-instance. -/
theorem perfectDisp_padInstance_iff [Fintype σ.Symbol] {k₀ r k : Nat}
    (p : Instance σ k₀ k₀) (hk₀r : k₀ ≤ r) (hrk : r ≤ k) :
    PerfectDisp (padInstance p hk₀r hrk) ↔ BIJ p := by
  rw [perfectDisp_iff_fin, bij_iff_fin]
  constructor
  · rintro ⟨n, hn, I, hI⟩
    haveI : NeZero n := ⟨by omega⟩
    rw [termMap_padInstance, padMap_surjective_iff] at hI
    exact ⟨n, hn, I, (surjective_iff_bijective_square p I).1 hI⟩
  · rintro ⟨n, hn, I, hI⟩
    haveI : NeZero n := ⟨by omega⟩
    refine ⟨n, hn, I, ?_⟩
    rw [termMap_padInstance, padMap_surjective_iff]
    exact hI.2

/-- The exact size identity `‖padInstance p‖ + 2 k₀ = ‖p‖ + 2 r`. -/
theorem size_padInstance {k₀ r k : Nat} (p : Instance σ k₀ k₀)
    (hk₀r : k₀ ≤ r) (hrk : r ≤ k) :
    (padInstance p hk₀r hrk).size + 2 * k₀ = p.size + 2 * r := by
  let F : Nat → Nat := fun n => if h : n < k₀ then (p ⟨n, h⟩).size else 1
  have hpad : ∑ i : Fin r, (padInstance p hk₀r hrk i).size = ∑ i ∈ Finset.range r, F i := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp only [padInstance, F]
    by_cases h : i.val < k₀
    · rw [dif_pos h, dif_pos h, Term.size_mapVar]
    · rw [dif_neg h, dif_neg h]
      rfl
  have hp : ∑ j : Fin k₀, (p j).size = ∑ i ∈ Finset.range k₀, F i := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    simp only [F]
    rw [dif_pos j.isLt]
  have hsplit := Finset.sum_range_add_sum_Ico F hk₀r
  have hIco : ∑ i ∈ Finset.Ico k₀ r, F i = r - k₀ := by
    rw [Finset.sum_congr rfl (g := fun _ => 1)]
    · simp
    · intro i hi
      simp only [F]
      rw [dif_neg (by simpa using (Finset.mem_Ico.mp hi).1)]
  unfold Instance.size
  rw [hpad, hp, ← hsplit, hIco]
  omega

/-- Linear output-size bound `‖padInstance p‖ ≤ ‖p‖ + 2 r`. -/
theorem size_padInstance_le {k₀ r k : Nat} (p : Instance σ k₀ k₀)
    (hk₀r : k₀ ≤ r) (hrk : r ≤ k) :
    (padInstance p hk₀r hrk).size ≤ p.size + 2 * r := by
  have := size_padInstance p hk₀r hrk
  omega

/-- `thm:reduction-kk`: for every fixed `k ≥ 3`, `BIJ_3 ≤_m Perfect-Disp_k`
on square instances, via `padInstance`. -/
def reduction_kk [Fintype σ.Symbol] (k : Nat) (hk : 3 ≤ k) :
    ManyOneReduction (BIJ (σ := σ) (k := 3)) (PerfectDisp (σ := σ) (k := k) (r := k)) where
  map := fun p => padInstance p hk le_rfl
  correct := fun p => (perfectDisp_padInstance_iff p hk le_rfl).symm
  a := 1
  b := 2 * k
  size_le := fun p => by simpa using size_padInstance_le p hk le_rfl

/-- `thm:reduction-nr`: for every fixed pair `k ≥ r ≥ 3`,
`BIJ_3 ≤_m Perfect-Disp_r` on the subfamily with exactly `k` inputs and `r`
outputs, via `padInstance`. -/
def reduction_nr [Fintype σ.Symbol] (k r : Nat) (hr : 3 ≤ r) (hrk : r ≤ k) :
    ManyOneReduction (BIJ (σ := σ) (k := 3)) (PerfectDisp (σ := σ) (k := k) (r := r)) where
  map := fun p => padInstance p hr hrk
  correct := fun p => (perfectDisp_padInstance_iff p hr hrk).symm
  a := 1
  b := 2 * r
  size_le := fun p => by simpa using size_padInstance_le p hr hrk

/-- The conditional consequence recorded in `thm:reduction-kk` /
`thm:reduction-nr`: if `BIJ_3` were undecidable then so would be
`Perfect-Disp_r`, phrased as the contrapositive transfer of any decision
procedure along the reduction (no undecidability is asserted). -/
def decidable_bij3_of_decidable_perfect [Fintype σ.Symbol] (k r : Nat)
    (hr : 3 ≤ r) (hrk : r ≤ k)
    (dec : ∀ t : Instance σ k r, Decidable (PerfectDisp t)) :
    ∀ p : Instance σ 3 3, Decidable (BIJ p) :=
  fun p => decidable_of_iff _ (perfectDisp_padInstance_iff p hr hrk)

end Dispersion

end TermCoding
