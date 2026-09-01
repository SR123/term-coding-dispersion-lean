import TermCoding.Dispersion.Basic
import TermCoding.Dispersion.SquareBijectivity
import TermCoding.Dispersion.DirectPower
import TermCoding.Dispersion.OneOutput

/-!
# The perfect-alphabet spectrum (V10, `def:perfect-spectrum`,
`thm:perfect-spectrum-structure`(i), `thm:one-output`, remark "The
borderline output dimension `r = 2`")

`perfectSpectrum t = {n : ℕ | 2 ≤ n ∧ Disp_n(t) = n ^ r}` packages exact
surjectivity across all finite alphabet sizes (V10 Definition
`def:perfect-spectrum`).

* `perfectSpectrum_nonempty_iff` — `Perfect-Disp(t)` asks whether the
  spectrum is nonempty.
* `mul_mem_perfectSpectrum` — multiplicative closure
  (`thm:perfect-spectrum-structure`(i)), via the product-alphabet
  interpretation `productInterp`.
* `pow_mem_perfectSpectrum` — the power special case (`m ≥ 1`).
* `mem_perfectSpectrum_single_iff`, `perfectSpectrum_single_of_hasVar`,
  `perfectSpectrum_single_of_ground`, `perfectSpectrum_single_dichotomy` —
  the complete one-output classification (`thm:one-output`,
  `thm:landscape`(ii), `cor:bij-one`): if a variable occurs the spectrum is
  all of `{n | 2 ≤ n}`, otherwise it is empty.
* `mem_perfectSpectrum_square_iff` — for square instances, membership at
  size `n ≥ 2` is the existence of a bijective witness on `Fin n`
  (`lem:square-perfect-equals-bij` at a fixed size).
* `perfectDisp_two_iff_bij_two` — the `r = 2` borderline remark: the square
  subfamily of `Perfect-Disp_2` is exactly `BIJ_2`.
-/

namespace TermCoding

namespace Dispersion

universe uSym

variable {σ : Signature.{uSym}} [Fintype σ.Symbol] {k r : Nat}

/-- V10 `def:perfect-spectrum`: the set of alphabet sizes `n ≥ 2` at which
`t` is perfectly dispersive. -/
def perfectSpectrum (t : Instance σ k r) : Set ℕ :=
  {n : ℕ | 2 ≤ n ∧ dispN t n = n ^ r}

theorem mem_perfectSpectrum_iff (t : Instance σ k r) {n : ℕ} :
    n ∈ perfectSpectrum t ↔ 2 ≤ n ∧ dispN t n = n ^ r := Iff.rfl

/-- `Perfect-Disp(t)` holds iff the perfect-alphabet spectrum is nonempty
(V10, sentence after `def:perfect-spectrum`). -/
theorem perfectSpectrum_nonempty_iff (t : Instance σ k r) :
    (perfectSpectrum t).Nonempty ↔ PerfectDisp t := by
  constructor
  · rintro ⟨n, hn, h⟩; exact ⟨n, hn, h⟩
  · rintro ⟨n, hn, h⟩; exact ⟨n, hn, h⟩

/-- `thm:perfect-spectrum-structure`(i): the perfect-alphabet spectrum is
multiplicatively closed. -/
theorem mul_mem_perfectSpectrum {t : Instance σ k r} {a b : ℕ}
    (ha : a ∈ perfectSpectrum t) (hb : b ∈ perfectSpectrum t) :
    a * b ∈ perfectSpectrum t := by
  obtain ⟨ha2, hda⟩ := ha
  obtain ⟨hb2, hdb⟩ := hb
  refine ⟨Nat.le_trans ha2 (Nat.le_mul_of_pos_right a (by omega)), ?_⟩
  exact dispN_mul_eq_of_perfect t (by omega) (by omega) hda hdb

/-- `thm:perfect-spectrum-structure`(i), power form: if `n` is in the
spectrum then so is `n ^ m` for every `m ≥ 1`. -/
theorem pow_mem_perfectSpectrum {t : Instance σ k r} {n : ℕ}
    (hn : n ∈ perfectSpectrum t) {m : ℕ} (hm : 1 ≤ m) :
    n ^ m ∈ perfectSpectrum t := by
  obtain ⟨hn2, hd⟩ := hn
  refine ⟨le_trans hn2 (Nat.le_self_pow (by omega) n), ?_⟩
  exact dispN_pow_eq_of_perfect t (by omega) hd m

/-! ### The complete one-output classification (`thm:one-output`) -/

/-- Membership in the one-output spectrum: every size `n ≥ 2` works as soon
as some input variable occurs in the single output term. -/
theorem mem_perfectSpectrum_single_iff (t : Instance σ k 1) {n : ℕ} :
    n ∈ perfectSpectrum t ↔ 2 ≤ n ∧ ∃ j, Term.HasVar j (t 0) := by
  constructor
  · rintro ⟨hn2, hd⟩
    refine ⟨hn2, ?_⟩
    by_contra hno
    push_neg at hno
    have hground : Term.IsGround (t 0) := Term.isGround_of_not_hasVar (t 0) hno
    obtain ⟨I, hI⟩ := (dispN_eq_pow_iff t (by omega)).1 hd
    exact not_surjective_of_isGround (A := Fin n) (by simpa using hn2) (t 0) hground I
      ((surjective_termMap_single_iff t I).1 hI)
  · rintro ⟨hn2, j, hj⟩
    refine ⟨hn2, (dispN_eq_pow_iff t (by omega)).2 ?_⟩
    haveI : NeZero n := ⟨by omega⟩
    exact ⟨routingInterp (0 : Fin n),
      (surjective_termMap_single_iff t _).2 (surjective_of_hasVar (t 0) j hj 0)⟩

/-- `thm:one-output`, positive half: if some variable occurs, the spectrum
is all of `{n | 2 ≤ n}`. -/
theorem perfectSpectrum_single_of_hasVar (t : Instance σ k 1)
    (h : ∃ j, Term.HasVar j (t 0)) :
    perfectSpectrum t = {n : ℕ | 2 ≤ n} := by
  ext n
  rw [mem_perfectSpectrum_single_iff]
  exact ⟨fun ⟨hn, _⟩ => hn, fun hn => ⟨hn, h⟩⟩

/-- `thm:one-output`, negative half: if no variable occurs, the spectrum is
empty. -/
theorem perfectSpectrum_single_of_ground (t : Instance σ k 1)
    (h : ¬ ∃ j, Term.HasVar j (t 0)) :
    perfectSpectrum t = ∅ := by
  ext n
  rw [mem_perfectSpectrum_single_iff]
  simp [h]

/-- `thm:landscape`(ii): the one-output spectrum is either empty or all
sizes `n ≥ 2`. -/
theorem perfectSpectrum_single_dichotomy (t : Instance σ k 1) :
    perfectSpectrum t = ∅ ∨ perfectSpectrum t = {n : ℕ | 2 ≤ n} := by
  by_cases h : ∃ j, Term.HasVar j (t 0)
  · exact Or.inr (perfectSpectrum_single_of_hasVar t h)
  · exact Or.inl (perfectSpectrum_single_of_ground t h)

/-! ### Square instances -/

/-- For a square instance, membership of `n ≥ 2` in the spectrum is the
existence of a bijective witness on `Fin n`
(`lem:square-perfect-equals-bij`, fixed-size form). -/
theorem mem_perfectSpectrum_square_iff (t : Instance σ k k) {n : ℕ}
    (hn : 2 ≤ n) :
    n ∈ perfectSpectrum t ↔
      ∃ I : Interpretation σ (Fin n), Function.Bijective (termMap t I) := by
  rw [mem_perfectSpectrum_iff]
  constructor
  · rintro ⟨-, hd⟩
    obtain ⟨I, hI⟩ := (dispN_eq_pow_iff t (by omega)).1 hd
    exact ⟨I, (surjective_iff_bijective_square t I).1 hI⟩
  · rintro ⟨I, hI⟩
    exact ⟨hn, (dispN_eq_pow_iff t (by omega)).2
      ⟨I, (surjective_iff_bijective_square t I).2 hI⟩⟩

/-- V10 remark "The borderline output dimension `r = 2`": on square
instances with two inputs and two outputs, `Perfect-Disp_2` is exactly
`BIJ_2`. -/
theorem perfectDisp_two_iff_bij_two (t : Instance σ 2 2) :
    PerfectDisp t ↔ BIJ t :=
  perfectDisp_iff_bij t

end Dispersion

end TermCoding
