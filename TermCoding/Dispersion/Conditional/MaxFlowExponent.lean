import TermCoding.Dispersion.Exponent
import TermCoding.Dispersion.TermCut
import TermCoding.Dispersion.Threshold
import TermCoding.Dispersion.SquareBijectivity
import TermCoding.Dispersion.Reductions
import TermCoding.Dispersion.OneOutput
import TermCoding.Dispersion.Routing

/-!
# Conditional layer: consequences of the 2019 max-flow exponent theorem

**No project-level postulate is declared here.**  Everything in this file is
a theorem whose statement carries the external input as an explicit
hypothesis.

## The exact imported statement

Riis–Gadouleau 2019, Theorem 1 (with Lemma 3 for the upper bound and the
dynamic-routing construction, Definition 9 and Lemma 4, for the lower
bound): for a term set `Γ` with min term-cut `ρ` (Definition 2 there;
formalised as `termCutNumber`),

* for every alphabet `A`, `|Im Θ^I| ≤ |A|^ρ` for every interpretation
  (**proved here**: `dispN_le_pow_termCutNumber`), and
* for every alphabet with `|A| > |Γ_sub|` there is an interpretation whose
  image has at least `(|B| − 1)^ρ` elements, where
  `|A| = |Γ_sub|·|B| + |R|` with `1 ≤ |R| ≤ |Γ_sub|`; consequently
  `Disp_n(Γ) ≥ c·n^ρ` for all large `n` with an explicit `c > 0`
  (**external**: `MaxFlowLowerBound`).

V6's `thm:disp-exponent` is the conjunction of these with "`D(t)` is
computable in polynomial time"; the complexity clause is not a statement
about the sequence `Disp_n(t)` and is classified separately in the reports.

The routing construction of the source is itself formalised in
`TermCoding.Dispersion.Routing`, so the external hypothesis shrinks further:
`maxFlowLowerBound_of_pathSystem` derives `MaxFlowLowerBound t` from a
family of `ρ(t)` vertex-disjoint variable-to-output paths in the term DAG,
and `maxFlowLowerBound_of_menger` from `MengerForTerms t`.  What remains
external for a general instance is exactly Menger's classical theorem
(min vertex cut = max vertex-disjoint paths) for the term DAG; for any
concrete instance the paths can be exhibited (see `diamondPathSystem`).

## What follows from the hypothesis

* `exponentData_of_lowerBound` -- the full `ExponentData` (Θ statement with
  uniform upper bound).
* `exponent_eq_termCutNumber` -- `D(t) = ρ(t)`: the limit is the integer
  min-cut (integrality of `D(t)`).
* `threshold_iff_of_lowerBound` -- `thm:ptime-threshold`, the equivalence
  "eventual threshold ⇔ `ρ(t) ≥ d + 1`" for every threshold function
  satisfying `eq:threshold-conditions`.
* `fullRate_iff_termCutNumber`, `fullRate_iff_eventual` -- `Full-Rate-Disp`
  is `ρ(t) = r`, equivalently the eventual condition
  `Disp_n(t) ≥ n^{r−1} + 1`.
* `perfect_implies_termCutNumber_eq` -- perfect dispersion forces `ρ(t) = r`.

Unconditionally (no hypothesis): `exponent_le_termCutNumber` (`D(t) ≤ ρ(t)`),
`exponent_le_outputs`, `exponent_nonneg`.
-/

namespace TermCoding

namespace Dispersion

open Filter

universe uSym

variable {σ : Signature.{uSym}} [Fintype σ.Symbol] {k r : Nat}

/-- The external input, stated exactly: the lower half of Theorem 1 of
Riis–Gadouleau 2019 for the instance `t`, in the `Θ` form used by V6. -/
def MaxFlowLowerBound (t : Instance σ k r) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N : Nat, ∀ n, N ≤ n → c * (n : ℝ) ^ termCutNumber t ≤ dispN t n

/-- With the (proved) uniform upper bound, the external lower bound gives the
full numerical exponent data with `D = ρ(t)`. -/
theorem exponentData_of_lowerBound (t : Instance σ k r) (h : MaxFlowLowerBound t) :
    ExponentData (dispN t) (termCutNumber t) :=
  ⟨fun _ hn => dispN_le_pow_termCutNumber t hn, h⟩

/-! ### Unconditional bounds on the exponent -/

/-- `1 ≤ Disp_n(t)` for `n ≥ 1`: the image of a map with nonempty domain is
nonempty. -/
theorem one_le_dispN (t : Instance σ k r) {n : Nat} (hn : 1 ≤ n) : 1 ≤ dispN t n := by
  haveI : NeZero n := ⟨by omega⟩
  let I : Interpretation σ (Fin n) := fun _ _ => 0
  refine le_trans ?_ (imageCard_le_disp (A := Fin n) t I)
  unfold imageCard
  have : Nonempty (Set.range (termMap t I)) := ⟨⟨termMap t I (fun _ => 0), ⟨_, rfl⟩⟩⟩
  exact Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨this, Set.finite_range _⟩)

/-- Whenever `Disp_n(t) ≤ n^D` for all `n ≥ 2`, the limit `D(t)` is at most `D`. -/
theorem exponent_le_of_upper (t : Instance σ k r) (hr : 0 < r) {D : Nat}
    (hD : ∀ n, 2 ≤ n → dispN t n ≤ n ^ D) : exponent t ≤ D := by
  refine le_of_tendsto (dispRate_tendsto t hr) ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hpos : (0 : ℝ) < dispN t n := by exact_mod_cast one_le_dispN t (by omega)
  have hup : (dispN t n : ℝ) ≤ (n : ℝ) ^ D := by exact_mod_cast hD n hn
  unfold dispRate
  rw [div_le_iff₀ hlogpos]
  have := Real.log_le_log hpos hup
  rwa [Real.log_pow] at this

/-- `D(t) ≤ ρ(t)` unconditionally (from the proved cut upper bound). -/
theorem exponent_le_termCutNumber (t : Instance σ k r) (hr : 0 < r) :
    exponent t ≤ termCutNumber t :=
  exponent_le_of_upper t hr (fun n hn => dispN_le_pow_termCutNumber t (by omega))

/-- `D(t) ≤ r` unconditionally. -/
theorem exponent_le_outputs (t : Instance σ k r) (hr : 0 < r) : exponent t ≤ r :=
  exponent_le_of_upper t hr (fun n _ => dispN_le_pow t n)

/-- `0 ≤ D(t)` unconditionally. -/
theorem exponent_nonneg (t : Instance σ k r) (hr : 0 < r) : 0 ≤ exponent t := by
  refine ge_of_tendsto (dispRate_tendsto t hr) ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have h1 : (1 : ℝ) ≤ dispN t n := by exact_mod_cast one_le_dispN t (by omega)
  unfold dispRate
  exact div_nonneg (Real.log_nonneg h1) hlogpos.le

/-! ### Consequences of the external lower bound -/

/-- `D(t) = ρ(t)`: the limit is the integer min-cut. -/
theorem exponent_eq_termCutNumber (t : Instance σ k r) (hr : 0 < r)
    (h : MaxFlowLowerBound t) : exponent t = termCutNumber t :=
  tendsto_nhds_unique (dispRate_tendsto t hr)
    (by rw [dispRate_eq_rate]; exact rate_tendsto (exponentData_of_lowerBound t h))

/-- `thm:ptime-threshold` for term dispersion: the eventual threshold
condition holds iff `ρ(t) ≥ d + 1`. -/
theorem threshold_iff_of_lowerBound (t : Instance σ k r) (h : MaxFlowLowerBound t)
    {d : Nat} {hd : Nat → Nat} (hh : ThresholdConditions d hd) :
    (∃ N : Nat, ∀ n, N ≤ n → hd n ≤ dispN t n) ↔ d + 1 ≤ termCutNumber t :=
  threshold_iff (exponentData_of_lowerBound t h) hh

/-- `Full-Rate-Disp(t) ⇔ ρ(t) = r`. -/
theorem fullRate_iff_termCutNumber (t : Instance σ k r) (hr : 0 < r)
    (h : MaxFlowLowerBound t) : FullRateDisp t ↔ termCutNumber t = r := by
  unfold FullRateDisp
  rw [exponent_eq_termCutNumber t hr h]
  exact_mod_cast Iff.rfl

/-- The eventual-threshold form of full rate (README, item 5):
`D(t) = r ⇔ ∃ N ∀ n ≥ N, Disp_n(t) ≥ n^{r−1} + 1`. -/
theorem fullRate_iff_eventual (t : Instance σ k r) (hr : 0 < r)
    (h : MaxFlowLowerBound t) :
    FullRateDisp t ↔ ∃ N : Nat, ∀ n, N ≤ n → n ^ (r - 1) + 1 ≤ dispN t n := by
  rw [fullRate_iff_termCutNumber t hr h,
    threshold_iff_of_lowerBound t h (thresholdConditions_pow_add_one (r - 1))]
  have hle := termCutNumber_le_outputs t
  omega

/-- Perfect dispersion forces `ρ(t) = r` (the integer form of
`thm:perfect-implies-full-rate`). -/
theorem perfect_implies_termCutNumber_eq (t : Instance σ k r) (hr : 0 < r)
    (h : MaxFlowLowerBound t) (hp : PerfectDisp t) : termCutNumber t = r :=
  (fullRate_iff_termCutNumber t hr h).1 (fullRateDisp_of_perfectDisp t hr hp)

/-- The diamond satisfies the external lower bound unconditionally (its
min-cut is `4` and `Disp_n ≥ n^4/4096`). -/
theorem maxFlowLowerBound_diamond : MaxFlowLowerBound diamond := by
  unfold MaxFlowLowerBound
  rw [termCutNumber_diamond]
  exact exponentData_diamond.lower

/-! ### Discharging the hypothesis from a path certificate -/

/-- A family of `ρ(t)` vertex-disjoint paths proves the external lower
bound: the entire "dynamic routing" half of the 2019 theorem is
kernel-checked (`TermCoding.Dispersion.Routing`); only the *existence* of a
maximum path family (Menger) is instance-specific. -/
theorem maxFlowLowerBound_of_pathSystem (t : Instance σ k r) (hr : 0 < r)
    (P : PathSystem t (termCutNumber t)) : MaxFlowLowerBound t :=
  pathSystem_lowerBound_real P hr

/-- `MaxFlowLowerBound` from Menger's theorem for the term DAG of `t`. -/
theorem maxFlowLowerBound_of_menger (t : Instance σ k r) (hr : 0 < r)
    (h : MengerForTerms t) : MaxFlowLowerBound t := by
  obtain ⟨P⟩ := h
  exact maxFlowLowerBound_of_pathSystem t hr P

end Dispersion

end TermCoding
