import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# The analytic threshold theorem (V6, `thm:ptime-threshold`, layer 1)

This file is purely about a numerical sequence `Disp : ℕ → ℕ`; it does not
mention terms.  It isolates exactly what the manuscript uses from
`thm:disp-exponent`:

* `ExponentData Disp D` -- an integer `D` with the *uniform* upper bound
  `Disp n ≤ n^D` for every `n ≥ 1` and an *eventual* lower bound
  `c·n^D ≤ Disp n` with an explicit constant `c > 0` (this is the
  `Θ(n^D)` statement of `thm:disp-exponent` together with its "for every
  `n`" clause).
* `ThresholdConditions d h` -- the two printed hypotheses
  `eq:threshold-conditions` on the fixed threshold function `h = h_d`:
  eventually `n^d < h n`, and `h ∈ o(n^{d+1})` in the sense of Mathlib's
  `Asymptotics.IsLittleO` along `Filter.atTop` (real-valued, via the
  natural-number coercion).
* `threshold_iff` -- the exact equivalence
  `(∃ N, ∀ n ≥ N, h n ≤ Disp n) ↔ d + 1 ≤ D`.  The "yes" direction uses
  little-o with the lower-bound constant `c`; the "no" direction uses the
  uniform upper bound for every `n`.
* `rate_tendsto` -- `log (Disp n) / log n → D`; the base of the logarithm is
  irrelevant since only ratios occur (Mathlib's `Real.log` is natural).

The polynomial-time conclusion of `thm:ptime-threshold` is *not* a
statement about this sequence; it is discussed in the reports
(`04_TRUST_BOUNDARY.md`).
-/

namespace TermCoding

namespace Dispersion

open Filter Asymptotics

/-- The numerical content imported from `thm:disp-exponent`. -/
structure ExponentData (Disp : ℕ → ℕ) (D : ℕ) : Prop where
  /-- The uniform bound `Disp_n ≤ n^D`, valid for every `n ≥ 1`. -/
  upper : ∀ n, 1 ≤ n → Disp n ≤ n ^ D
  /-- The eventual lower bound `c·n^D ≤ Disp_n` with an explicit `c > 0`. -/
  lower : ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n, N ≤ n → c * (n : ℝ) ^ D ≤ Disp n

/-- The two conditions `eq:threshold-conditions` on a threshold function. -/
structure ThresholdConditions (d : ℕ) (h : ℕ → ℕ) : Prop where
  /-- `∃ N₀ ∀ n ≥ N₀, n^d < h(n)`. -/
  eventually_gt : ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → n ^ d < h n
  /-- `h(n) ∈ o(n^{d+1})`. -/
  littleO : (fun n : ℕ => (h n : ℝ)) =o[atTop] (fun n : ℕ => (n : ℝ) ^ (d + 1))

/-- `h_d(n) = n^d + 1` satisfies the threshold conditions. -/
theorem thresholdConditions_pow_add_one (d : ℕ) :
    ThresholdConditions d (fun n => n ^ d + 1) := by
  refine ⟨⟨0, fun n _ => by omega⟩, ?_⟩
  have h1 : (fun n : ℕ => ((n ^ d + 1 : ℕ) : ℝ)) =
      fun n : ℕ => (n : ℝ) ^ d + 1 := by
    funext n
    push_cast
    ring
  rw [h1]
  apply IsLittleO.add
  · -- `n^d = o(n^{d+1})`
    have : (fun n : ℕ => (n : ℝ) ^ d) =o[atTop] fun n : ℕ => (n : ℝ) ^ (d + 1) := by
      have hpow := (isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) (Nat.lt_succ_self d))
      exact hpow.comp_tendsto tendsto_natCast_atTop_atTop
    exact this
  · -- `1 = o(n^{d+1})`
    have hpow := (isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) (Nat.succ_pos d))
    have h0 : (fun x : ℝ => x ^ 0) = fun _ : ℝ => (1 : ℝ) := by
      funext x
      simp
    rw [h0] at hpow
    exact hpow.comp_tendsto tendsto_natCast_atTop_atTop

/-- `thm:ptime-threshold`, analytic core: the eventual threshold condition
holds iff `D ≥ d + 1`. -/
theorem threshold_iff {Disp : ℕ → ℕ} {D d : ℕ} {h : ℕ → ℕ}
    (hD : ExponentData Disp D) (hh : ThresholdConditions d h) :
    (∃ N : ℕ, ∀ n, N ≤ n → h n ≤ Disp n) ↔ d + 1 ≤ D := by
  constructor
  · -- the "no" direction: `D ≤ d` contradicts the uniform bound eventually
    rintro ⟨N, hN⟩
    by_contra hlt
    push_neg at hlt
    obtain ⟨N₀, hN₀⟩ := hh.eventually_gt
    let n := max (max N N₀) 1
    have hn1 : 1 ≤ n := le_max_right _ _
    have hnN : N ≤ n := (le_max_left _ _).trans (le_max_left _ _)
    have hnN₀ : N₀ ≤ n := (le_max_right _ _).trans (le_max_left _ _)
    have h1 : Disp n ≤ n ^ D := hD.upper n hn1
    have h2 : n ^ D ≤ n ^ d := Nat.pow_le_pow_right hn1 (by omega)
    have h3 : n ^ d < h n := hN₀ n hnN₀
    have h4 : h n ≤ Disp n := hN n hnN
    omega
  · -- the "yes" direction: little-o with the lower-bound constant `c`
    intro hdD
    obtain ⟨c, hc, N₁, hN₁⟩ := hD.lower
    have hev : ∀ᶠ n : ℕ in atTop, ‖(h n : ℝ)‖ ≤ c * ‖(n : ℝ) ^ (d + 1)‖ :=
      hh.littleO.def hc
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hev
    refine ⟨max (max N₁ N₂) 1, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
    have hnN₁ : N₁ ≤ n := ((le_max_left _ _).trans (le_max_left _ _)).trans hn
    have hnN₂ : N₂ ≤ n := ((le_max_right _ _).trans (le_max_left _ _)).trans hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hlittle := hN₂ n hnN₂
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at hlittle
    have hpow : (n : ℝ) ^ (d + 1) ≤ (n : ℝ) ^ D := pow_le_pow_right₀ hnR hdD
    have hlow := hN₁ n hnN₁
    have hreal : (h n : ℝ) ≤ Disp n := by
      calc (h n : ℝ) ≤ c * (n : ℝ) ^ (d + 1) := hlittle
        _ ≤ c * (n : ℝ) ^ D := by gcongr
        _ ≤ Disp n := hlow
    exact_mod_cast hreal

/-- The decision rule of `thm:ptime-threshold`: compare the integer exponent
with `d + 1`.  (Computing the exponent itself is the external step.) -/
def decideThreshold (D d : ℕ) : Bool := decide (d + 1 ≤ D)

theorem decideThreshold_correct {Disp : ℕ → ℕ} {D d : ℕ} {h : ℕ → ℕ}
    (hD : ExponentData Disp D) (hh : ThresholdConditions d h) :
    decideThreshold D d = true ↔ ∃ N : ℕ, ∀ n, N ≤ n → h n ≤ Disp n := by
  rw [threshold_iff hD hh]
  simp [decideThreshold]

/-! ### The exponent is the limit of the logarithmic rate -/

/-- The logarithmic rate `log Disp_n / log n`. -/
noncomputable def rate (Disp : ℕ → ℕ) (n : ℕ) : ℝ :=
  Real.log (Disp n) / Real.log n

/-- `log Disp_n / log n → D` under `ExponentData` (squeeze between
`D + log c / log n` and `D`). -/
theorem rate_tendsto {Disp : ℕ → ℕ} {D : ℕ} (hD : ExponentData Disp D) :
    Tendsto (rate Disp) atTop (nhds (D : ℝ)) := by
  obtain ⟨c, hc, N, hN⟩ := hD.lower
  have hlogn : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlower : Tendsto (fun n : ℕ => (D : ℝ) + Real.log c / Real.log n) atTop
      (nhds ((D : ℝ) + 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hlogn)
  rw [add_zero] at hlower
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower tendsto_const_nhds ?_ ?_
  · -- eventual lower bound
    filter_upwards [eventually_ge_atTop (max N 2)] with n hn
    have hnN : N ≤ n := (le_max_left _ _).trans hn
    have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have hlow := hN n hnN
    have hnpos : (0 : ℝ) < n := by linarith
    have hDpos : (0 : ℝ) < Disp n := lt_of_lt_of_le (by positivity) hlow
    have hlog : Real.log c + D * Real.log n ≤ Real.log (Disp n) := by
      have := Real.log_le_log (by positivity) hlow
      rwa [Real.log_mul hc.ne' (by positivity), Real.log_pow] at this
    unfold rate
    rw [le_div_iff₀ hlogpos, add_mul, div_mul_cancel₀ _ hlogpos.ne']
    linarith
  · -- uniform upper bound
    filter_upwards [eventually_ge_atTop (max N 2)] with n hn
    have hnN : N ≤ n := (le_max_left _ _).trans hn
    have hn2 : 2 ≤ n := (le_max_right _ _).trans hn
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn2
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have hup : (Disp n : ℝ) ≤ (n : ℝ) ^ D := by exact_mod_cast hD.upper n (by omega)
    have hlow := hN n hnN
    have hDpos : (0 : ℝ) < Disp n := lt_of_lt_of_le (by positivity) hlow
    have hlog : Real.log (Disp n) ≤ D * Real.log n := by
      have := Real.log_le_log hDpos hup
      rwa [Real.log_pow] at this
    unfold rate
    rw [div_le_iff₀ hlogpos]
    exact hlog

end Dispersion

end TermCoding
