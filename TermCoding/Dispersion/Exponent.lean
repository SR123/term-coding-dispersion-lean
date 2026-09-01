import TermCoding.Dispersion.Basic
import TermCoding.Dispersion.Diamond
import TermCoding.Dispersion.DirectPower
import TermCoding.Dispersion.Threshold
import TermCoding.Examples.DispersionTermCoding
import TermCoding.Exponent

/-!
# The dispersion exponent as a limit (V6, Sections 5.3 and 6.2)

The manuscript defines `D(t) := lim_{n→∞} log Disp_n(t) / log n` and obtains
the *existence* of the limit from the imported max-flow theorem.  Existence
is in fact a theorem of the Paper 1 development: by `lem:disp-embed`
(`Examples.Dispersion.codingTheoryMax_eq_dispersionMax`) the sequence
`Disp_n(t)` is the maximum code size `S_n(Γ_t)` of the decoder-augmented term
theory `Γ_t`, and Paper 1's finite-sandwich exponent theorem
(`TermTheory.maxSolutionRate_tendsto`) shows that `log S_n(Γ_t) / log n`
converges.

* `disp_eq_dispersionMax`, `termMap_eq_paper1` -- exact declaration-level
  match with the Paper 1 construction.
* `dispN_eq_codingTheoryMax` -- `lem:disp-embed`: `Disp_n(t) = S_n(Γ_t)`
  for every `n ≥ 1`.
* `exponent t` -- `D(t)`, a real number; `dispRate_tendsto` -- it is the
  limit of `log Disp_n(t) / log n` (fully checked; integrality is *not*
  claimed here).
* `limit_eq_of_perfect` -- `thm:perfect-implies-full-rate` from an explicit
  convergence hypothesis; `exponent_eq_of_perfect` -- its unconditional
  instantiation: perfect dispersion on some finite alphabet forces
  `D(t) = r`.  This uses only the direct-power lemma and the existence of
  the limit.
* `exponentData_diamond`, `exponent_diamond` -- the diamond has
  `Disp_n = Θ(n^4)` and `D = 4`, proved from the explicit routing
  interpretation; together with `diamond_not_perfect` this is the "converse
  fails" clause, also unconditional.
-/

namespace TermCoding

namespace Dispersion

open Filter

universe uSym uAlpha

variable {σ : Signature.{uSym}} [Fintype σ.Symbol] {k r : Nat}

/-! ### Exact match with the Paper 1 dispersion construction -/

omit [Fintype σ.Symbol] in
/-- `termMap` is the Paper 1 term map. -/
theorem termMap_eq_paper1 {A : Type uAlpha} (t : Instance σ k r) (I : Interpretation σ A) :
    termMap t I = Examples.Dispersion.termMap t I := rfl

/-- `disp` is the Paper 1 `dispersionMax` of the same family of term maps. -/
theorem disp_eq_dispersionMax (A : Type uAlpha) [Fintype A] (t : Instance σ k r) :
    disp A t =
      Examples.Dispersion.dispersionMax
        (fun I : Interpretation σ A => Examples.Dispersion.termMap t I) := by
  unfold disp Examples.Dispersion.dispersionMax
  congr 1

/-- `lem:disp-embed` on an abstract finite alphabet: `Disp_A(t) = S_A(Γ_t)`,
where `Γ_t` is the decoder-augmented term theory of Paper 1. -/
theorem disp_eq_codingTheoryMax (A : Type uAlpha) [Fintype A] [Nonempty A]
    (t : Instance σ k r) :
    disp A t =
      TermTheory.maxSolutionCount (A := A) (Examples.Dispersion.codingTheory t) := by
  rw [disp_eq_dispersionMax, Examples.Dispersion.codingTheoryMax_eq_dispersionMax]

/-- `lem:disp-embed`: `Disp_n(t) = S_n(Γ_t)` for every `n ≥ 1`. -/
theorem dispN_eq_codingTheoryMax (t : Instance σ k r) {n : Nat} (hn : 1 ≤ n) :
    dispN t n =
      TermTheory.maxSolutionCount (A := Fin n) (Examples.Dispersion.codingTheory t) := by
  haveI : NeZero n := ⟨by omega⟩
  exact disp_eq_codingTheoryMax (Fin n) t

/-! ### The exponent -/

/-- The logarithmic rate `log Disp_n(t) / log n`. -/
noncomputable def dispRate (t : Instance σ k r) (n : Nat) : ℝ :=
  Real.log (dispN t n) / Real.log n

theorem dispRate_eq_rate (t : Instance σ k r) : dispRate t = rate (dispN t) := rfl

/-- `D(t)`: the exponent of the decoder-augmented term theory `Γ_t` in the
sense of Paper 1 (the supremal guessing rate of its canonical normal form).
`dispRate_tendsto` shows this is `lim log Disp_n(t) / log n`. -/
noncomputable def exponent (t : Instance σ k r) : ℝ :=
  TermTheory.exponent (Examples.Dispersion.codingTheory t)

instance codingVarNonempty_of_pos_r (hr : 0 < r) : Nonempty (Examples.Dispersion.CodingVar k r) :=
  ⟨Sum.inr ⟨0, hr⟩⟩

/-- `log Disp_n(t) / log n → D(t)`: the limit defining the dispersion
exponent exists.  Proved from Paper 1's sandwich exponent theorem via
`lem:disp-embed`; no max-flow input. -/
theorem dispRate_tendsto (t : Instance σ k r) (hr : 0 < r) :
    Tendsto (dispRate t) atTop (nhds (exponent t)) := by
  haveI : Nonempty (Examples.Dispersion.CodingVar k r) := ⟨Sum.inr ⟨0, hr⟩⟩
  have h := TermTheory.maxSolutionRate_tendsto (Examples.Dispersion.codingTheory t)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  unfold TermTheory.maxSolutionRate dispRate
  rw [dispN_eq_codingTheoryMax t hn]

/-- `Full-Rate-Disp(t)`: `D(t) = r`. -/
def FullRateDisp (t : Instance σ k r) : Prop := exponent t = r

/-- Along the alphabet sizes `n^m` a perfectly dispersive instance has rate
exactly `r`. -/
theorem dispRate_pow_eq_of_perfect (t : Instance σ k r) {n : Nat} (hn : 2 ≤ n)
    (h : dispN t n = n ^ r) {m : Nat} (hm : 1 ≤ m) : dispRate t (n ^ m) = r := by
  unfold dispRate
  rw [dispN_pow_eq_of_perfect t (by omega) h m]
  have hpos : (1 : ℝ) < ((n ^ m : Nat) : ℝ) := by
    have : 1 < n ^ m := Nat.one_lt_pow (by omega) (by omega)
    exact_mod_cast this
  have hlog : Real.log ((n ^ m : Nat) : ℝ) ≠ 0 := (Real.log_pos hpos).ne'
  rw [Nat.cast_pow ((n ^ m : Nat)) r, Real.log_pow]
  field_simp

/-- `thm:perfect-implies-full-rate` from an explicit convergence hypothesis:
if `log Disp_n(t) / log n → L` and `t` is perfectly dispersive on some finite
alphabet, then `L = r`.  This is exactly the manuscript's argument (the limit
along the subsequence `n^m` equals `r`). -/
theorem limit_eq_of_perfect (t : Instance σ k r) {L : ℝ}
    (hlim : Tendsto (dispRate t) atTop (nhds L)) (h : PerfectDisp t) : L = r := by
  obtain ⟨n, hn, hperf⟩ := h
  have hpow : Tendsto (fun m : Nat => n ^ m) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by omega)
  have hsub : Tendsto (fun m : Nat => dispRate t (n ^ m)) atTop (nhds L) :=
    hlim.comp hpow
  have hconst : Tendsto (fun m : Nat => dispRate t (n ^ m)) atTop (nhds (r : ℝ)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with m hm
    exact (dispRate_pow_eq_of_perfect t hn hperf hm).symm
  exact tendsto_nhds_unique hsub hconst

/-- `thm:perfect-implies-full-rate` (first sentence): perfect dispersion on
some finite alphabet forces `D(t) = r`.  Unconditional: the convergence
hypothesis of `limit_eq_of_perfect` is supplied by `dispRate_tendsto`. -/
theorem exponent_eq_of_perfect (t : Instance σ k r) (hr : 0 < r) (h : PerfectDisp t) :
    exponent t = r :=
  limit_eq_of_perfect t (dispRate_tendsto t hr) h

/-- `Perfect-Disp ⊆ Full-Rate-Disp`. -/
theorem fullRateDisp_of_perfectDisp (t : Instance σ k r) (hr : 0 < r) (h : PerfectDisp t) :
    FullRateDisp t :=
  exponent_eq_of_perfect t hr h

/-! ### The diamond: full rate without perfect dispersion -/

/-- The diamond satisfies the numerical exponent specification with `D = 4`:
`Disp_n ≤ n^4` for all `n ≥ 1` and `Disp_n ≥ n^4 / 4096` for `n ≥ 8`. -/
theorem exponentData_diamond : ExponentData (dispN diamond) 4 := by
  refine ⟨fun n _ => dispN_le_pow diamond n, ⟨1 / 4096, by norm_num, 8, ?_⟩⟩
  intro n hn
  have hnat := div_pow_le_dispN_diamond n (by omega)
  have hcast : (((n / 4) ^ 4 : Nat) : ℝ) ≤ (dispN diamond n : ℝ) := by exact_mod_cast hnat
  have hdiv : (n : ℝ) / 8 ≤ ((n / 4 : Nat) : ℝ) := by
    have h1 : n < 4 * (n / 4) + 4 := by
      have := Nat.lt_mul_div_succ n (show 0 < 4 by norm_num)
      omega
    have h2 : (n : ℝ) < 4 * ((n / 4 : Nat) : ℝ) + 4 := by exact_mod_cast h1
    have h3 : (8 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hnonneg : (0 : ℝ) ≤ (n : ℝ) / 8 := by positivity
  calc (1 / 4096 : ℝ) * (n : ℝ) ^ 4 = ((n : ℝ) / 8) ^ 4 := by ring
    _ ≤ ((n / 4 : Nat) : ℝ) ^ 4 := by gcongr
    _ = (((n / 4) ^ 4 : Nat) : ℝ) := by push_cast; ring
    _ ≤ dispN diamond n := hcast

/-- `D(diamond) = 4` (the value asserted in `lem:diamond-maxflow`), proved
without the external theorem. -/
theorem exponent_diamond : exponent diamond = 4 := by
  have h1 := dispRate_tendsto diamond (by norm_num)
  have h2 := rate_tendsto exponentData_diamond
  rw [dispRate_eq_rate] at h1
  have := tendsto_nhds_unique h1 h2
  simpa using this

/-- The diamond has full rate. -/
theorem fullRateDisp_diamond : FullRateDisp diamond := by
  unfold FullRateDisp
  rw [exponent_diamond]
  norm_num

/-- `thm:perfect-implies-full-rate`, "the converse fails": full rate does
not imply perfect dispersion. -/
theorem not_perfect_of_fullRate_fails :
    ∃ t : Instance diamondSignature 4 4, FullRateDisp t ∧ ¬ PerfectDisp t :=
  ⟨diamond, fullRateDisp_diamond, diamond_not_perfect⟩

end Dispersion

end TermCoding
