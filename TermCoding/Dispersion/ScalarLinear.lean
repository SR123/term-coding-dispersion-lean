import TermCoding.Dispersion.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.FieldTheory.Finite.Polynomial
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Scalar-linear witnesses (V6, Section 7.3, `prop:scalar-det-criterion-main`)

A *scalar-linear interpretation* over a field `K` interprets every `q`-ary
symbol `s` as `s(v_1,…,v_q) = λ_{s,1} v_1 + ⋯ + λ_{s,q} v_q` with scalars
`λ_{s,j} ∈ K`.  Introducing one commuting indeterminate per argument slot
`(s, j)`, every term `u` in `k` variables has a *symbolic coefficient vector*
`coeff u ∈ ℤ[λ]^k`, and a square tuple `t` has a symbolic coefficient matrix
`C_t ∈ M_k(ℤ[λ])` with determinant `Δ_t`.

* `eval_scalarLinearInterp` -- under a scalar-linear interpretation every
  term is the linear form with coefficients `coeff u` evaluated at `λ`.
* `termMap_scalarLinear` -- `Θ^I` is the matrix–vector map of `C_t(λ)`.
* `bijective_scalarLinear_iff` -- `Θ^I` is bijective iff `Δ_t(λ) ≠ 0`.
* `scalarLinearWitness_iff` -- `prop:scalar-det-criterion-main`: `t` has a
  scalar-linear witness over `K` iff some assignment of scalars in `K` makes
  `Δ_t` nonzero.
* `scalarLinearWitness_decidable` -- over a finite field the witness question
  is a finite search (first "consequently" clause).
* `exists_primeField_witness_iff` -- the third clause in the form: `t` has a
  scalar-linear witness over some prime field `𝔽_p` iff `Δ_t ≠ 0` in
  `ℤ[λ]` (a witness over any field forces `Δ_t ≠ 0`; conversely a prime `p`
  not dividing some coefficient and exceeding the degree gives a witness by
  `MvPolynomial.eq_zero_of_eval_eq_zero`).

* `exists_galoisField_witness_iff` -- the second clause: for a fixed prime
  `p`, `t` has a scalar-linear witness over some extension `𝔽_{p^m}` iff
  `Δ_t` is nonvanishing as a polynomial over the prime field (i.e. its
  reduction mod `p` is nonzero).
-/

namespace TermCoding

namespace Dispersion

open MvPolynomial

universe uSym

/-- The argument slots `(s, j)` of a signature: one coefficient per slot. -/
abbrev Slot (σ : Signature.{uSym}) := (s : σ.Symbol) × Fin (σ.arity s)

section General

variable {σ : Signature.{uSym}} {k : Nat} {K : Type*} [CommRing K]

/-- The scalar-linear interpretation with coefficients `λ`. -/
def scalarLinearInterp (lam : Slot σ → K) : Interpretation σ K :=
  fun s input => ∑ j, lam ⟨s, j⟩ * input j

/-- The symbolic coefficient vector of a term (recursive construction of
`C_t`). -/
noncomputable def coeff : Term σ (Fin k) → Fin k → MvPolynomial (Slot σ) ℤ
  | .var i => fun j => if j = i then 1 else 0
  | .app s args => fun j => ∑ p, X ⟨s, p⟩ * coeff (args p) j

/-- Under a scalar-linear interpretation every term is a linear form in the
input variables with coefficients `coeff u` evaluated at `λ`. -/
theorem eval_scalarLinearInterp (lam : Slot σ → K) (x : Fin k → K) :
    ∀ u : Term σ (Fin k),
      u.eval (scalarLinearInterp lam) x = ∑ j, aeval lam (coeff u j) * x j
  | .var i => by
      simp only [Term.eval, coeff]
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [hj]
      · intro h
        exact absurd (Finset.mem_univ i) h
  | .app s args => by
      simp only [Term.eval, scalarLinearInterp, coeff]
      have ih : ∀ p, (args p).eval (scalarLinearInterp lam) x =
          ∑ j, aeval lam (coeff (args p) j) * x j :=
        fun p => eval_scalarLinearInterp lam x (args p)
      simp only [ih, map_sum, map_mul, aeval_X, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro p _
      ring

/-- The symbolic coefficient matrix `C_t ∈ M_k(ℤ[λ])` of a square tuple. -/
noncomputable def symbolicMatrix (t : Instance σ k k) :
    Matrix (Fin k) (Fin k) (MvPolynomial (Slot σ) ℤ) :=
  fun i j => coeff (t i) j

/-- `Δ_t := det C_t ∈ ℤ[λ]`. -/
noncomputable def symbolicDet (t : Instance σ k k) : MvPolynomial (Slot σ) ℤ :=
  (symbolicMatrix t).det

/-- `C_t(λ)`: the coefficient matrix evaluated at the chosen scalars. -/
noncomputable def coeffMatrix (t : Instance σ k k) (lam : Slot σ → K) :
    Matrix (Fin k) (Fin k) K :=
  (symbolicMatrix t).map (aeval lam)

theorem det_coeffMatrix (t : Instance σ k k) (lam : Slot σ → K) :
    (coeffMatrix t lam).det = aeval lam (symbolicDet t) := by
  unfold coeffMatrix symbolicDet
  rw [AlgHom.map_det]
  rfl

/-- `Θ^I` is the matrix–vector map of `C_t(λ)`. -/
theorem termMap_scalarLinear (t : Instance σ k k) (lam : Slot σ → K) :
    termMap t (scalarLinearInterp lam) = (coeffMatrix t lam).mulVec := by
  funext x i
  simp only [termMap, Matrix.mulVec, dotProduct, coeffMatrix, symbolicMatrix, Matrix.map_apply]
  exact eval_scalarLinearInterp lam x (t i)

end General

section Field

variable {σ : Signature.{uSym}} {k : Nat} {K : Type*} [Field K]

/-- `Θ^I` is bijective iff `Δ_t(λ) ≠ 0`. -/
theorem bijective_scalarLinear_iff (t : Instance σ k k) (lam : Slot σ → K) :
    Function.Bijective (termMap t (scalarLinearInterp lam)) ↔
      aeval lam (symbolicDet t) ≠ 0 := by
  rw [termMap_scalarLinear, ← det_coeffMatrix, ← isUnit_iff_ne_zero,
    ← Matrix.isUnit_iff_isUnit_det]
  constructor
  · intro h
    exact Matrix.mulVec_injective_iff_isUnit.1 h.1
  · intro h
    exact ⟨Matrix.mulVec_injective_iff_isUnit.2 h, Matrix.mulVec_surjective_iff_isUnit.2 h⟩

/-- `t` has a scalar-linear witness over `K`. -/
def ScalarLinearWitness (t : Instance σ k k) (K : Type*) [Field K] : Prop :=
  ∃ lam : Slot σ → K, Function.Bijective (termMap t (scalarLinearInterp lam))

/-- `prop:scalar-det-criterion-main`. -/
theorem scalarLinearWitness_iff (t : Instance σ k k) :
    ScalarLinearWitness t K ↔ ∃ lam : Slot σ → K, aeval lam (symbolicDet t) ≠ 0 := by
  unfold ScalarLinearWitness
  simp only [bijective_scalarLinear_iff]

/-- Over a finite field the witness question is a finite search over the
finitely many coefficient assignments (first "consequently" clause).  The
decision procedure evaluates the determinant at each assignment. -/
noncomputable instance scalarLinearWitness_decidable (t : Instance σ k k)
    [Fintype σ.Symbol] [Fintype K] [DecidableEq K] : Decidable (ScalarLinearWitness t K) := by
  classical
  exact decidable_of_iff _ (scalarLinearWitness_iff t).symm

/-- A witness over any field forces `Δ_t ≠ 0` as an integer polynomial. -/
theorem symbolicDet_ne_zero_of_witness (t : Instance σ k k) (h : ScalarLinearWitness t K) :
    symbolicDet t ≠ 0 := by
  obtain ⟨lam, hlam⟩ := (scalarLinearWitness_iff t).1 h
  intro h0
  apply hlam
  rw [h0, map_zero]

end Field

section PrimeField

variable {σ : Signature.{0}} {k : Nat}

/-- For every prime `p` not dividing some coefficient of a nonzero integer
polynomial and exceeding its total degree, the reduction mod `p` has a
nonzero evaluation over `𝔽_p`. -/
theorem exists_eval_ne_zero_zmod {ι : Type} [Finite ι] (F : MvPolynomial ι ℤ)
    (hF : F ≠ 0) :
    ∃ p : ℕ, p.Prime ∧ ∃ lam : ι → ZMod p, aeval lam F ≠ 0 := by
  classical
  obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.1 hF
  set c := MvPolynomial.coeff d F with hc
  obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes (max (c.natAbs + 1) (F.totalDegree + 2))
  haveI := Fact.mk hp
  refine ⟨p, hp, ?_⟩
  -- the reduction of `F` mod `p`
  let G : MvPolynomial ι (ZMod p) := MvPolynomial.map (Int.castRingHom (ZMod p)) F
  have hG : G ≠ 0 := by
    intro h0
    have : MvPolynomial.coeff d G = 0 := by rw [h0]; simp
    rw [MvPolynomial.coeff_map] at this
    simp only [eq_intCast] at this
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    have hcne : c ≠ 0 := hd
    have hle : (p : ℤ) ≤ c.natAbs := by
      have := Int.natAbs_dvd_natAbs.2 this
      simp only [Int.natAbs_natCast] at this
      exact_mod_cast Nat.le_of_dvd (Int.natAbs_pos.2 hcne) this
    have : c.natAbs + 1 ≤ p := (le_max_left _ _).trans hp_ge
    omega
  -- degree restriction: every exponent is at most `totalDegree F ≤ p - 1`
  have hdeg : G ∈ restrictDegree ι (ZMod p) (Fintype.card (ZMod p) - 1) := by
    rw [MvPolynomial.mem_restrictDegree]
    intro s hs i
    have hs' : s ∈ F.support := MvPolynomial.support_map_subset (Int.castRingHom (ZMod p)) F hs
    have h1 : s i ≤ F.totalDegree := by
      have := MvPolynomial.le_totalDegree hs'
      calc s i ≤ s.sum (fun _ e => e) := by
            rw [Finsupp.sum]
            by_cases hi : i ∈ s.support
            · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
            · simp [Finsupp.notMem_support_iff.1 hi]
        _ ≤ F.totalDegree := this
    have h2 : F.totalDegree + 2 ≤ p := (le_max_right _ _).trans hp_ge
    rw [ZMod.card]
    omega
  by_contra hno
  push_neg at hno
  apply hG
  refine MvPolynomial.eq_zero_of_eval_eq_zero ι (ZMod p) G (fun v => ?_) hdeg
  have := hno v
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq_eval_map] at this
  simpa [G] using this

/-- Third "consequently" clause of Section 7.3, in prime-field form: `t` has
a scalar-linear witness over some prime field `𝔽_p` iff `Δ_t` is a nonzero
integer polynomial. -/
theorem exists_primeField_witness_iff [Fintype σ.Symbol] (t : Instance σ k k) :
    (∃ p : ℕ, ∃ _ : Fact p.Prime, ScalarLinearWitness t (ZMod p)) ↔ symbolicDet t ≠ 0 := by
  constructor
  · rintro ⟨p, hp, h⟩
    exact symbolicDet_ne_zero_of_witness t h
  · intro h
    obtain ⟨p, hp, lam, hlam⟩ := exists_eval_ne_zero_zmod (symbolicDet t) h
    haveI := Fact.mk hp
    exact ⟨p, ⟨hp⟩, (scalarLinearWitness_iff t).2 ⟨lam, hlam⟩⟩

/-- `cor:scalar-linear-classification`(c), literal form: a scalar-linear
witness exists over some finite field (of arbitrary characteristic) iff
`Δ_t` is a nonzero polynomial in `ℤ[λ]`.  The forward direction holds for a
witness over *any* field (`symbolicDet_ne_zero_of_witness`); the reverse
produces a prime-field witness. -/
theorem exists_finiteField_witness_iff [Fintype σ.Symbol] (t : Instance σ k k) :
    (∃ (K : Type) (_ : Field K) (_ : Fintype K), ScalarLinearWitness t K) ↔
      symbolicDet t ≠ 0 := by
  constructor
  · rintro ⟨K, _, _, h⟩
    exact symbolicDet_ne_zero_of_witness t h
  · intro h
    obtain ⟨p, hp, hw⟩ := (exists_primeField_witness_iff t).2 h
    haveI : Fact p.Prime := hp
    exact ⟨ZMod p, inferInstance, inferInstance, hw⟩

end PrimeField

section GaloisExtensions

open MvPolynomial

variable {σ : Signature.{0}} {k : Nat}

/-- Reduction mod `p` of an integer polynomial. -/
noncomputable def modP (p : ℕ) {ι : Type} (F : MvPolynomial ι ℤ) :
    MvPolynomial ι (ZMod p) :=
  MvPolynomial.map (Int.castRingHom (ZMod p)) F

/-- Evaluating an integer polynomial in a `ZMod p`-algebra factors through
its reduction mod `p`. -/
theorem aeval_int_eq_aeval_modP (p : ℕ) {ι : Type} (K : Type) [CommRing K]
    [Algebra (ZMod p) K] (lam : ι → K) (F : MvPolynomial ι ℤ) :
    aeval lam F = aeval lam (modP p F) := by
  unfold modP
  rw [aeval_def, aeval_def, eval₂_eq_eval_map, eval₂_eq_eval_map, MvPolynomial.map_map,
    show (algebraMap (ZMod p) K).comp (Int.castRingHom (ZMod p)) = Int.castRingHom K from
      RingHom.ext_int _ _, algebraMap_int_eq]

/-- A nonzero polynomial over `𝔽_p` has a nonzero evaluation over the finite
extension `𝔽_{p^{D+2}}`, `D` its total degree
(`MvPolynomial.eq_zero_of_eval_eq_zero`). -/
theorem exists_eval_ne_zero_galoisField (p : ℕ) [Fact p.Prime] {ι : Type} [Finite ι]
    (F : MvPolynomial ι (ZMod p)) (hF : F ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ lam : ι → GaloisField p m, aeval lam F ≠ 0 := by
  classical
  set m := F.totalDegree + 2 with hm
  refine ⟨m, by omega, ?_⟩
  letI : Fintype (GaloisField p m) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p m) = p ^ m := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card p m (by omega)
  -- the image of `F` in the extension is nonzero
  let G : MvPolynomial ι (GaloisField p m) :=
    MvPolynomial.map (algebraMap (ZMod p) (GaloisField p m)) F
  have hG : G ≠ 0 := by
    intro h0
    exact hF (MvPolynomial.map_injective _ (algebraMap (ZMod p) (GaloisField p m)).injective
      (h0.trans (map_zero (MvPolynomial.map (algebraMap (ZMod p) (GaloisField p m)))).symm))
  -- degree restriction: `p^m` exceeds every exponent
  have hdeg : G ∈ restrictDegree ι (GaloisField p m) (Fintype.card (GaloisField p m) - 1) := by
    rw [MvPolynomial.mem_restrictDegree]
    intro sup hs i
    have hs' : sup ∈ F.support := MvPolynomial.support_map_subset _ _ hs
    have h1 : sup i ≤ F.totalDegree := by
      have hle := MvPolynomial.le_totalDegree hs'
      calc sup i ≤ sup.sum (fun _ e => e) := by
            rw [Finsupp.sum]
            by_cases hi : i ∈ sup.support
            · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
            · simp [Finsupp.notMem_support_iff.1 hi]
        _ ≤ F.totalDegree := hle
    have h2 : F.totalDegree + 2 ≤ 2 ^ m := by
      rw [hm]
      exact le_of_lt Nat.lt_two_pow_self
    have h3 : 2 ^ m ≤ p ^ m := Nat.pow_le_pow_left (Fact.out : p.Prime).two_le m
    rw [hcard]
    omega
  by_contra hno
  push_neg at hno
  apply hG
  refine MvPolynomial.eq_zero_of_eval_eq_zero ι (GaloisField p m) G (fun v => ?_) hdeg
  have hv := hno v
  rw [aeval_def, eval₂_eq_eval_map] at hv
  simpa [G] using hv

/-- Second "consequently" clause of Section 7.3: for a fixed prime `p`, a
scalar-linear witness exists over some extension `𝔽_{p^m}` iff `Δ_t` is
nonvanishing as a polynomial over the prime field. -/
theorem exists_galoisField_witness_iff [Fintype σ.Symbol] (t : Instance σ k k)
    (p : ℕ) [Fact p.Prime] :
    (∃ m : ℕ, 0 < m ∧ ScalarLinearWitness t (GaloisField p m)) ↔
      modP p (symbolicDet t) ≠ 0 := by
  constructor
  · rintro ⟨m, hm, h⟩
    obtain ⟨lam, hlam⟩ := (scalarLinearWitness_iff t).1 h
    intro h0
    apply hlam
    rw [aeval_int_eq_aeval_modP p _ lam, h0, map_zero]
  · intro h
    obtain ⟨m, hm, lam, hlam⟩ := exists_eval_ne_zero_galoisField p (modP p (symbolicDet t)) h
    refine ⟨m, hm, (scalarLinearWitness_iff t).2 ⟨lam, ?_⟩⟩
    rw [aeval_int_eq_aeval_modP p _ lam]
    exact hlam

end GaloisExtensions

end Dispersion

end TermCoding
