import TermCoding.Dispersion.Basic
import TermCoding.Dispersion.Diamond
import TermCoding.Dispersion.OneOutput
import TermCoding.Dispersion.Padding
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin

/-!
# Adversarial checks on degenerate parameters (prompt Section 7, items 1, 4, 6)

* Zero outputs: `Perfect-Disp` is trivially a yes-instance (`n^0 = 1`).
* Zero inputs (`k = 0`, `r ≥ 1`): all output terms are ground, the image has
  one point, and perfect dispersion fails on every alphabet of size `≥ 2`.
* Singleton alphabet: `Disp_1(t) = 1 = 1^r`, so "perfect at `n = 1`" always
  holds -- this is why the decision problems require `n ≥ 2`.
* Empty alphabet with `k ≥ 1`: `Disp_0(t) = 0 = 0^r` for `r ≥ 1`, another
  reason for the restriction.
* Repeated arguments and shared symbols: `f(x,x)` is a one-output
  yes-instance; the ordered-tuple semantics of `termMap` is definitional.
* Tree size versus DAG size: `doublingTerm n = f(u,u)` iterated has tree size
  `2^{n+1} − 1` while its shared term DAG has `n + 1` nodes, so the remark
  that the two encodings are "polynomially related" is false in general
  (`size_doublingTerm`; the DAG count is in `Paper1Bridge`).
-/

namespace TermCoding

namespace Dispersion

universe uSym

variable {σ : Signature.{uSym}} [Fintype σ.Symbol] {k r : Nat}

/-- With no output terms every image is the one-point set. -/
theorem dispN_eq_one_of_r_zero (t : Instance σ k 0) {n : Nat} (hn : 1 ≤ n) :
    dispN t n = 1 := by
  haveI : NeZero n := ⟨by omega⟩
  apply le_antisymm
  · simpa using dispN_le_pow t n
  · exact (dispN_eq_pow_iff t hn).2 ⟨fun _ _ => 0, fun y => ⟨fun _ => 0, by
      funext i; exact Fin.elim0 i⟩⟩ ▸ le_rfl

/-- `r = 0`: every instance is a `Perfect-Disp` yes-instance. -/
theorem perfectDisp_of_r_zero (t : Instance σ k 0) : PerfectDisp t :=
  ⟨2, le_rfl, by simpa using dispN_eq_one_of_r_zero t (by norm_num : 1 ≤ 2)⟩

/-- `k = 0`, `r ≥ 1`: all terms are ground, so perfect dispersion fails on
every alphabet of size at least two. -/
theorem not_perfectDisp_of_k_zero (t : Instance σ 0 r) (hr : 0 < r) : ¬ PerfectDisp t := by
  rw [perfectDisp_iff_fin]
  rintro ⟨n, hn, I, hI⟩
  haveI : NeZero n := ⟨by omega⟩
  have hground : ∀ i, Term.IsGround (t i) := fun i =>
    Term.isGround_of_not_hasVar (t i) (fun v _ => Fin.elim0 v)
  obtain ⟨y₀, hy₀⟩ := hI (fun _ => (0 : Fin n))
  obtain ⟨y₁, hy₁⟩ := hI (fun _ => (1 : Fin n))
  have : termMap t I y₀ = termMap t I y₁ := by
    funext i
    exact Term.eval_eq_of_isGround I y₀ y₁ (t i) (hground i)
  rw [hy₀, hy₁] at this
  have h := congrFun this ⟨0, hr⟩
  have h01 : (0 : Fin n) ≠ 1 := by
    intro h'
    have := congrArg Fin.val h'
    rw [Fin.val_zero, Fin.val_one'] at this
    have h2 : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
    omega
  exact h01 h

/-- Singleton alphabet: `Disp_1(t) = 1`. -/
theorem dispN_one (t : Instance σ k r) : dispN t 1 = 1 := by
  apply le_antisymm
  · simpa using dispN_le_pow t 1
  · exact (dispN_eq_pow_iff t le_rfl).2 ⟨fun _ _ => 0, fun y => ⟨fun _ => 0, by
      funext i; exact Subsingleton.elim _ _⟩⟩ ▸ (by simp)

/-- Every instance is "perfect at `n = 1`": the restriction `n ≥ 2` in the
decision problems is necessary. -/
theorem perfectDispAt_one (t : Instance σ k r) : PerfectDispAt t 1 := by
  unfold PerfectDispAt
  rw [dispN_one]
  simp

/-- Empty alphabet with at least one input: `Disp_0(t) = 0`. -/
theorem dispN_zero (t : Instance σ k r) (hk : 0 < k) : dispN t 0 = 0 := by
  apply le_antisymm _ (Nat.zero_le _)
  have := dispN_le_pow_dom t 0
  rw [Nat.zero_pow hk] at this
  exact this

/-- `Disp_0(t) = 0^r` when `k, r ≥ 1`: "perfect at `n = 0`" holds vacuously. -/
theorem perfectDispAt_zero (t : Instance σ k r) (hk : 0 < k) (hr : 0 < r) :
    PerfectDispAt t 0 := by
  unfold PerfectDispAt
  rw [dispN_zero t hk, Nat.zero_pow hr]

/-- Repeated arguments: the one-output instance `f(x,x)` over the diamond
signature is a `Perfect-Disp_1` yes-instance. -/
theorem perfectDisp_repeated_argument :
    PerfectDisp (![fapp (.var 0) (.var 0)] : Instance diamondSignature 1 1) := by
  rw [perfectDisp_single_iff]
  exact ⟨0, ⟨(0 : Fin 2), rfl⟩⟩

/-- Ordered-tuple semantics with repetition, definitionally. -/
theorem termMap_repeated_argument {A : Type} (g : A → A → A) (x : Fin 1 → A) :
    termMap (![fapp (.var 0) (.var 0)] : Instance diamondSignature 1 1) (diamondInterp g) x
      (0 : Fin 1) = g (x 0) (x 0) := rfl

/-- `u_0 = x`, `u_{n+1} = f(u_n, u_n)`: exponentially large syntax tree,
linear-size DAG. -/
def doublingTerm : Nat → Term diamondSignature (Fin 1)
  | 0 => .var 0
  | n + 1 => fapp (doublingTerm n) (doublingTerm n)

theorem size_fapp {V : Type} (a b : Term diamondSignature V) :
    (fapp a b).size = 1 + (a.size + b.size) := by
  simp only [fapp, Term.size]
  rw [show (∑ p : Fin (diamondSignature.arity ()), (![a, b] p).size) =
    ∑ p : Fin 2, (![a, b] p).size from rfl, Fin.sum_univ_two]
  rfl

/-- The tree size of `doublingTerm n` is `2^{n+1} − 1`. -/
theorem size_doublingTerm (n : Nat) : (doublingTerm n).size = 2 ^ (n + 1) - 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [doublingTerm, size_fapp, ih]
      have : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
      rw [pow_succ 2 (n + 1)]
      omega

end Dispersion

end TermCoding
