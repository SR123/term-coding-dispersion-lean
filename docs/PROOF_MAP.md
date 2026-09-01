# Proof map: V6 statements ↔ Lean declarations (copy of the audit report 02_PAPER_TO_LEAN_MAP.md, updated 30 August 2026)

For every item classified `Lean-checked` in `01_CLAIM_LEDGER.md` this table
gives the LaTeX label, the exact printed statement, the Lean declaration(s)
with their types (abridged), the axioms reported by `#print axioms`
(`AxiomsAudit.lean`; every entry is a subset of
`[propext, Classical.choice, Quot.sound]`), and the statement-matching
notes required by the prompt (universes, finiteness, nonemptiness, arities,
variable/output counts, quantifier order, optimisation domain).

Project: `Paper2_Dispersion_Dichotomy/Formalisation/TermCodingDispersionLean/`.
All names below live in `TermCoding.Dispersion` unless written in full.

## Conventions and their matching to V6

| V6 object | Lean | Matching notes |
|---|---|---|
| signature `𝔽` with arities (including `0`) | `TermCoding.Signature` (Paper 1): `Symbol : Type uSym`, `arity : Symbol → Nat` | arity `0` allowed; finiteness of the signature enters as `[Fintype σ.Symbol]` exactly where a maximum over interpretations is taken |
| terms over `𝔽` and variables `x_1..x_k` | `TermCoding.Term σ (Fin k)` | ordered argument tuples with repetition; shared subterms are identical terms |
| interpretation `𝓘` on `A` | `TermCoding.Interpretation σ A := (s : σ.Symbol) → (Fin (σ.arity s) → A) → A` | one *total* operation table per symbol, used at every occurrence |
| dispersion instance `t(x) = (t_1..t_r)`, `k` inputs | `Instance σ k r := Fin r → Term σ (Fin k)` | `k`, `r` are explicit type indices, so "exactly `k` inputs and `r` outputs" is enforced by types; V6 fixes `k, r ≥ 1` but only `r ≥ 1` (or nothing) is needed where stated |
| `Θ^𝓘 : A^k → A^r` | `termMap t I : (Fin k → A) → (Fin r → A)`, `= fun x i => (t i).eval I x` | definitionally `Examples.Dispersion.termMap` of Paper 1 (`termMap_eq_paper1 : … := rfl`) |
| `Disp_n(t) = max_𝓘 |Im Θ^𝓘|` | `disp A t := Finset.univ.sup (fun I : Interpretation σ A => imageCard t I)`; `dispN t n := disp (Fin n) t` | maximum over **all** interpretations of the *original* signature `σ` on the finite alphabet `A`; `disp_eq_dispersionMax` shows it is Paper 1's `dispersionMax` (`congr` on the `Fintype` instance); `disp_congr_equiv` shows only `|A|` matters (justifies `A = [n]`) |
| `|A| ≥ 2`, `n ≥ 2` | explicit hypotheses `2 ≤ Fintype.card A`, `2 ≤ n` | degenerate values checked in `Attacks.lean` |
| "finite set `A`" in `∃`-statements | `∃ (A : Type) (_ : Fintype A), …` (universe `0`) | `bij_iff_fin`, `perfectDisp_iff_fin` reduce to `Fin n`; by `disp_congr_equiv` no generality is lost |

## Section 5

### `lem:diamond-not-bij`
*Printed.* For every `n ≥ 2` and every interpretation `f^𝓘 : A^2 → A`, the
map `Θ^𝓘 : A^4 → A^4` of `eq:diamond-terms` is not injective (hence not
bijective/surjective).

*Lean.*
`diamond_not_injective {A} [Fintype A] (hA : 2 ≤ Fintype.card A) (I : Interpretation diamondSignature A) : ¬ Function.Injective (termMap diamond I)`;
`diamond_not_surjective … : ¬ Function.Surjective (termMap diamond I)`;
`dispN_diamond_lt (n) (hn : 2 ≤ n) : dispN diamond n < n ^ 4`;
`diamond_not_perfect : ¬ PerfectDisp diamond`.
Axioms: `[propext, Classical.choice, Quot.sound]`.
*Matching.* `diamondSignature` has one binary symbol; `diamond = ![f(x0,x1), f(x0,x2), f(x1,x3), f(x2,x3)]`; every interpretation is `diamondInterp g` (`diamondInterp_surjective`). The proof is the printed pigeonhole argument (`|A|^3 > |A|^2` used at exactly one place, `Nat.pow_lt_pow_right (by omega) (by omega)` from `2 ≤ |A|`).

### Remark "diversification removes the obstruction"
`diversifiedDiamond_bijective (A : Type*) : Function.Bijective (termMap diversifiedDiamond (diversifiedDiamondInterp A))` — the printed projections `f_1(x,y)=x, f_2(x,z)=z, f_3(y,w)=y, f_4(z,w)=w`; holds for every alphabet, finite or not. Axioms: `[propext, Quot.sound]` (subset).

### `lem:disp-embed`
*Printed.* For every `n ≥ 1`, `Disp_n(t) = S_n(Γ_t)`.
*Lean.* `dispN_eq_codingTheoryMax [Fintype σ.Symbol] (t : Instance σ k r) {n} (hn : 1 ≤ n) : dispN t n = TermTheory.maxSolutionCount (A := Fin n) (Examples.Dispersion.codingTheory t)`; abstract-alphabet form `disp_eq_codingTheoryMax`.
*Matching.* `Γ_t` is Paper 1's `codingTheory t : TermTheory (codingSignature σ k r) (CodingVar k r) (r + k)` with equations `t_i(x) = y_i` (`i < r`) and `h_j(y) = x_j` (`j < k`), `h_j` fresh `r`-ary — exactly `eq:disp-to-tc`. `S_n` maximises over interpretations of the *extended* signature (`Sum σ.Symbol (Fin k)`), as printed. The Paper 1 theorem `codingTheoryMax_eq_dispersionMax` needs `[Nonempty A]`, hence `n ≥ 1` (printed). Axioms: standard three.

### `thm:disp-exponent`, uniform upper bound (item (iii) of the "what we use" remark)
*Printed.* For every `n`, `Disp_n(t) ≤ n^{D(t)}` where `D(t)` is the min-cut of the source's network.
*Lean.* `ExprFrom`, `IsTermCut`, `termCutNumber t := sInf {ρ | ∃ C, IsTermCut t C ∧ C.card = ρ}` (the source's Definition 2, with cut elements arbitrary terms — superfluous non-subterms never help, so the minimum agrees with the source's "subterms only" formulation);
`imageCard_le_pow_card_of_termCut [Fintype A] [Nonempty A] (t) (C) (hC : IsTermCut t C) (I) : imageCard t I ≤ Fintype.card A ^ C.card` (Lemma 3 of the source);
`disp_le_pow_termCutNumber … : disp A t ≤ Fintype.card A ^ termCutNumber t`;
`dispN_le_pow_termCutNumber (t) {n} (hn : 1 ≤ n) : dispN t n ≤ n ^ termCutNumber t`.
Axioms: standard three.
*Matching.* Proved for every `n ≥ 1` (for `n = 0` the statement is trivial when `k ≥ 1`, `dispN_zero`). Constants (arity `0`) are expressible for free, as in the source ("applying function symbols").

### `lem:diamond-maxflow`
*Printed.* In the auxiliary network of the source the min cut has capacity `4`; consequently `D(t) = 4`.
*Lean.* `termCutNumber_diamond : termCutNumber diamond = 4`; `exponent_diamond : exponent diamond = 4`.
*Matching.* The value `4` is verified in the source's actual model (term-cuts). The proof of the lower bound `≥ 4` does not use the printed flow paths (which are not vertex-disjoint in the source's model, see finding F-04) but the routing interpretation `pow_le_dispN_diamond` (`m^4 ≤ Disp_{4m}`) against the proved cut bound: a cut of size `≤ 3` would give `Disp_{260} ≤ 260^3 < 65^4`. `D = 4` is proved from the same routing interpretation and the existence of the limit, **without** the max-flow theorem.

## Section 6

### `def:decision-problems`
`PerfectDispAt t n := dispN t n = n ^ r`; `PerfectDisp t := ∃ n, 2 ≤ n ∧ dispN t n = n ^ r`; `SurjectiveWitness t := ∃ (A : Type) (_ : Fintype A), 2 ≤ Fintype.card A ∧ ∃ I, Function.Surjective (termMap t I)`; `perfectDisp_iff_surjectiveWitness : PerfectDisp t ↔ SurjectiveWitness t` (the printed "equivalently"); `FullRateDisp t := exponent t = r`; `ThresholdConditions d h` (fixed parameters) and the eventual condition `∃ N, ∀ n ≥ N, h n ≤ dispN t n` used verbatim in `threshold_iff`. The fixed-`r` problems are the same predicates at a fixed type index.

### `lem:square-perfect-equals-bij`
*Printed.* For `t` with exactly `k` inputs and `k` outputs: (i) `∃ n ≥ 2, Disp_n(t) = n^k` ⇔ (ii) `∃` finite `A`, `|A| ≥ 2`, `𝓘` with `Θ^𝓘` surjective ⇔ (iii) … bijective.
*Lean.* `square_tfae (t : Instance σ k k) : [(∃ n, 2 ≤ n ∧ dispN t n = n ^ k), SurjectiveWitness t, BIJ t].TFAE`; `perfectDisp_iff_bij`, `surjectiveWitness_iff_bij`. Axioms: standard three.
*Matching.* (ii)⇔(iii) is `surjective_iff_bijective_square`, which uses `Finite A` and the equal domain/codomain type `Fin k → A` (`Finite.injective_iff_surjective`); (i)⇒(ii) uses that the maximum is attained (`exists_imageCard_eq_disp`, needs `Nonempty A`, supplied by `n ≥ 2`).

### `cor:bij-reduces-perfect`
`identity_reduction : ManyOneReduction (BIJ (σ := σ) (k := k)) (PerfectDisp (k := k) (r := k))` with `map := id`, `correct := perfectDisp_iff_bij`, size bound `a = 1, b = 0`. The fixed-`k` clause is the same declaration at fixed `k`. "Polynomial time" is documented by the identity map and the size identity; Lean has no cost model.

### `rem:inverse-extension`
`inverseSignature σ k` (`Sum σ.Symbol (Fin k)`, fresh `k`-ary `s_i`), `leftInverseEquation t i : s_i(t_1(x),…,t_k(x)) = x_i`, `rightInverseEquation t i : t_i(s_1(y),…,s_k(y)) = y_i` (built with `Term.subst`, `Term.eval_subst`);
`bijective_of_inverseEquations (t) (J) (hl : ∀ i x, (leftInverseEquation t i).Holds J x) (hr : ∀ i y, (rightInverseEquation t i).Holds J y) : Function.Bijective (termMap t (restrictInv J))`;
`exists_inverseExtension_of_bijective (t) (I) (h : Bijective (termMap t I)) : ∃ J, restrictInv J = I ∧ (∀ i x, …) ∧ (∀ i y, …)` — the fresh symbols are quantified freely and the original interpretation is unchanged;
`exists_inverseExtension_iff (t) : (∃ J, … ∧ …) ↔ ∃ I, Bijective (termMap t I)`.
Axioms: `[propext, Quot.sound]` / standard three.

### `lem:direct-power`
*Printed.* If `Θ^𝓘 : A^k → A^r` is surjective then for every `m ≥ 1` the coordinatewise `𝓘^{[m]}` on `A^m` makes `(A^m)^k → (A^m)^r` surjective.
*Lean.* `powerInterp m I : Interpretation σ (Fin m → A)` (coordinatewise for every arity, including `0`); `eval_powerInterp : u.eval (powerInterp m I) x = fun j => u.eval I (fun v => x v j)` (structural induction); `termMap_powerInterp_eq : termMap t (powerInterp m I) = (transpose r m).symm ∘ Pi.map (fun _ => termMap t I) ∘ transpose k m` with `transpose k m := Equiv.piComm` (the explicit coordinate transposition `(A^m)^k ≃ (A^k)^m`); `surjective_powerInterp (m) (t) (I) (h : Surjective (termMap t I)) : Surjective (termMap t (powerInterp m I))`; numerical form `dispN_pow_eq_of_perfect (hn : 1 ≤ n) (h : dispN t n = n ^ r) (m) : dispN t (n ^ m) = (n ^ m) ^ r`. Axioms: `Quot.sound` / `[Classical.choice, Quot.sound]`.
*Matching.* Holds for all `m` (including `m = 0`), arbitrary alphabet `A` (no finiteness needed for surjectivity), nested terms, repeated arguments and repeated occurrences of one symbol (one global table).

### `thm:perfect-implies-full-rate`
*Printed.* If `t` (with `r` outputs) has perfect dispersion on some finite alphabet then `D(t) = r`; hence `Perfect-Disp ⊆ Full-Rate-Disp`; the converse fails.
*Lean.* `exponent t : ℝ := TermTheory.exponent (codingTheory t)`; `dispRate_tendsto (t) (hr : 0 < r) : Tendsto (dispRate t) atTop (nhds (exponent t))` — i.e. `exponent t = lim log Disp_n(t)/log n`, the printed definition of `D(t)`, with existence **proved** (Paper 1's `TermTheory.maxSolutionRate_tendsto` through `lem:disp-embed`);
`limit_eq_of_perfect (t) {L} (hlim : Tendsto (dispRate t) atTop (nhds L)) (h : PerfectDisp t) : L = r` (the printed proof: rate `= r` along `n^m`);
`exponent_eq_of_perfect (t) (hr : 0 < r) (h : PerfectDisp t) : exponent t = r`;
`fullRateDisp_of_perfectDisp`; converse: `not_perfect_of_fullRate_fails : ∃ t : Instance diamondSignature 4 4, FullRateDisp t ∧ ¬ PerfectDisp t`.
Axioms: standard three.
*Matching.* V6 obtains the existence of the limit from `thm:disp-exponent`; the Lean proof obtains it from Paper 1 instead, so the theorem is **unconditional**. `r ≥ 1` is the printed standing assumption. Integrality of `D(t)` is not needed and not used.

### `lem:padding-outputs`
`padMap p hk₀r hrk : (Fin k → A) → (Fin r → A)` (`F(a) = (p(a_1..a_{k₀}), a_{k₀+1}..a_r)`); `padMap_surjective_iff [Nonempty A] (p) (hk₀r : k₀ ≤ r) (hrk : r ≤ k) : Surjective (padMap p …) ↔ Surjective p`. The hypothesis `Nonempty A` is not printed; `padMap_not_surjective_empty` shows the backward direction fails for `A = ∅`, `k₀ = r = 0`, `k = 1` (finding F-07; harmless under the paper's `|A| ≥ 2`). Axioms: standard three / `[propext, Quot.sound]`.

### `lem:unused-inputs`
`restrictMap f hrk`, `range_restrictMap [Nonempty A] : Set.range (restrictMap f hrk) = Set.range f` (the printed `Im F = Im f`), `restrictMap_surjective_iff`. Same nonemptiness caveat.

### `thm:reduction-kk`, `thm:reduction-nr`
Transformer `padInstance (p : Instance σ k₀ k₀) (hk₀r : k₀ ≤ r) (hrk : r ≤ k) : Instance σ k r`, `t_i = p_i[x ↦ castLE x]` for `i < k₀`, `t_i = x_i` for `k₀ ≤ i < r` (inputs `x_{r+1..k}` unused);
`termMap_padInstance : termMap (padInstance p …) I = padMap (termMap p I) …` (semantic correctness for every `I`);
`perfectDisp_padInstance_iff [Fintype σ.Symbol] : PerfectDisp (padInstance p hk₀r hrk) ↔ BIJ p` (yes/no preservation);
`size_padInstance : (padInstance p …).size + 2 * k₀ = p.size + 2 * r`, `size_padInstance_le : … ≤ p.size + 2 * r`;
`reduction_kk (k) (hk : 3 ≤ k) : ManyOneReduction (BIJ (k := 3)) (PerfectDisp (k := k) (r := k))`,
`reduction_nr (k r) (hr : 3 ≤ r) (hrk : r ≤ k) : ManyOneReduction (BIJ (k := 3)) (PerfectDisp (k := k) (r := r))`;
`decidable_bij3_of_decidable_perfect` (decidability transfer; the printed "if `BIJ_3` is undecidable then …" in contrapositive form, asserting nothing about `BIJ_3`).
Axioms: standard three. *Matching.* `k₀ = 3` as printed; `k ≥ r ≥ 3`; the alphabet nonemptiness needed by `padMap_surjective_iff` is supplied by `n ≥ 2`.

### `rem:k-less-r`
`disp_lt_pow_of_lt (t) (hkr : k < r) (hA : 2 ≤ Fintype.card A) : disp A t < Fintype.card A ^ r`.

### V10 spectrum layer (`def:perfect-spectrum`, `thm:perfect-spectrum-structure`, `prop:small-spectra`, `r = 2` remark)

| V10 statement | Lean declaration (`TermCoding.Dispersion`) |
|---|---|
| `def:perfect-spectrum` | `perfectSpectrum` (`Spectrum.lean`); `perfectSpectrum_nonempty_iff` ties it to `PerfectDisp` |
| `lem:product-surjectivity` | `productInterp`, `eval_productInterp`, `termMap_productInterp`, `surjective_productInterp` (`DirectPower.lean`) |
| `thm:perfect-spectrum-structure`(i) | `mul_mem_perfectSpectrum`, `pow_mem_perfectSpectrum`, numerical core `dispN_mul_eq_of_perfect` |
| `thm:perfect-spectrum-structure`(ii) | `exponent_eq_of_spectrum_nonempty` (`SpectrumExponent.lean`), core `exponent_eq_of_perfect` (unconditional) |
| `thm:perfect-spectrum-structure`(iii) | `exponent_diamond`, `diamond_not_perfect` |
| `thm:one-output` | `mem_perfectSpectrum_single_iff`, `perfectSpectrum_single_of_hasVar`, `perfectSpectrum_single_of_ground`, `perfectSpectrum_single_dichotomy` (`Spectrum.lean`); construction in `OneOutput.lean` |
| square fixed-size bridge | `mem_perfectSpectrum_square_iff` |
| remark "borderline `r = 2`" | `perfectDisp_two_iff_bij_two` |
| `prop:small-spectra` | `perfectSpectrum_tau_least`, `perfectSpectrum_sigma_least`, `pow_three_mem_perfectSpectrum_tau`, `pow_four_mem_perfectSpectrum_sigma`, `sigma_no_interpretation_three` (`SmallSpectra.lean`), kernel cores in `Experiments.lean` / `ExperimentsSigmaThree.lean` |
| `cor:scalar-linear-classification`(c) literal form | `exists_finiteField_witness_iff` (`ScalarLinear.lean`) |

### Remark "small output dimension", `r = 1`; Section 7.1 `BIJ_1`
`activeTuple P a c`, `prescribed P a c`, `prescription_consistent (P Q) (a b c) (h : activeTuple P a c = activeTuple Q b c) : prescribed P a c = prescribed Q b c` (the printed consistency claim, all cases including the all-`c` tuple);
`routingInterp c : Interpretation σ A` (one total table for every symbol extending all prescriptions);
`eval_routingInterp_slice (j) (a c) (u) : (HasVar j u → u.eval (routingInterp c) (sliceAssignment j a c) = a) ∧ (¬ HasVar j u → … = c)` (structural induction over nested terms, repeated symbols, constants);
`perfectDisp_single_iff [Fintype σ.Symbol] (t : Instance σ k 1) : PerfectDisp t ↔ ∃ j, Term.HasVar j (t 0)`;
`not_surjective_of_isGround (hA : 2 ≤ card A)`; `bij_one_iff (t : Instance σ 1 1) : BIJ t ↔ Term.HasVar 0 (t 0)`; `bijective_single_of_hasVar (h) (c : A) : Bijective (termMap t (routingInterp c))` (every alphabet with a point; V6: "every finite set of size `q ≥ 2` admits a witness").
Axioms: standard three.

### `thm:ptime-threshold`
Layer 1 (numerical): `ExponentData Disp D` (`upper : ∀ n, 1 ≤ n → Disp n ≤ n ^ D`; `lower : ∃ c > 0, ∃ N, ∀ n ≥ N, c * n^D ≤ Disp n`), `ThresholdConditions d h` (`eventually_gt : ∃ N₀, ∀ n ≥ N₀, n ^ d < h n`; `littleO : (fun n => (h n : ℝ)) =o[atTop] fun n => (n : ℝ) ^ (d + 1)`),
`threshold_iff (hD : ExponentData Disp D) (hh : ThresholdConditions d h) : (∃ N, ∀ n, N ≤ n → h n ≤ Disp n) ↔ d + 1 ≤ D`;
`decideThreshold D d := decide (d + 1 ≤ D)`, `decideThreshold_correct`; `thresholdConditions_pow_add_one d : ThresholdConditions d (fun n => n ^ d + 1)`; `rate_tendsto (hD) : Tendsto (rate Disp) atTop (nhds D)`.
Layer 2 (term dispersion, conditional): `threshold_iff_of_lowerBound (t) (h : MaxFlowLowerBound t) (hh) : (∃ N, ∀ n ≥ N, hd n ≤ dispN t n) ↔ d + 1 ≤ termCutNumber t`.
Axioms: standard three. *Matching.* `d`, `h_d` fixed parameters; `n ≥ 1` for the uniform bound; Mathlib `Asymptotics.IsLittleO` along `Filter.atTop` on the real coercions; the "yes" direction uses `IsLittleO.def` with `ε := c`, the "no" direction uses the uniform bound at one `n ≥ max(N, N₀, 1)`. Logarithm base irrelevant (`Real.log` ratios).

### `thm:landscape`
(i) `landscape_square`; (ii) `landscape_reduction`; (iii) `landscape_rate`. (iv), (v): mathematical content `fullRate_iff_termCutNumber`, `fullRate_iff_eventual`, `threshold_iff_of_lowerBound` (conditional); algorithmic part external.

## Section 7.3 — `prop:scalar-det-criterion-main`
`Slot σ := (s : σ.Symbol) × Fin (σ.arity s)`; `scalarLinearInterp lam s input := ∑ j, lam ⟨s, j⟩ * input j`; `coeff : Term σ (Fin k) → Fin k → MvPolynomial (Slot σ) ℤ` (recursive: `coeff (var i) = e_i`, `coeff (app s args) j = ∑ p, X⟨s,p⟩ * coeff (args p) j`); `symbolicMatrix t i j := coeff (t i) j`; `symbolicDet t := det (symbolicMatrix t)`;
`eval_scalarLinearInterp (lam) (x) (u) : u.eval (scalarLinearInterp lam) x = ∑ j, aeval lam (coeff u j) * x j`;
`termMap_scalarLinear : termMap t (scalarLinearInterp lam) = (coeffMatrix t lam).mulVec`; `det_coeffMatrix : (coeffMatrix t lam).det = aeval lam (symbolicDet t)`;
`bijective_scalarLinear_iff [Field K] : Bijective (termMap t (scalarLinearInterp lam)) ↔ aeval lam (symbolicDet t) ≠ 0`;
`scalarLinearWitness_iff : ScalarLinearWitness t K ↔ ∃ lam : Slot σ → K, aeval lam (symbolicDet t) ≠ 0`.
Consequences: `scalarLinearWitness_decidable` (finite `K`: finite search); `exists_primeField_witness_iff [Fintype σ.Symbol] (t) : (∃ p, ∃ _ : Fact p.Prime, ScalarLinearWitness t (ZMod p)) ↔ symbolicDet t ≠ 0` (prime-field form of the third clause; `σ : Signature.{0}` because of Mathlib's universe convention in `MvPolynomial.eq_zero_of_eval_eq_zero`).
Axioms: standard three. *Matching.* "assignment of the scalar coefficients in `K` for which `Δ_t ≠ 0`" is read as `aeval lam Δ_t ≠ 0`; coefficient ring `ℤ[λ_{s,j}]`, one indeterminate per argument slot, exactly as printed. The second clause (extensions of a fixed finite field) is not formalised.

## Section 7.1 — `k = 2` experiments
`tauPair`, `sigmaPair`; `tau_no_witness_two`, `sigma_no_witness_two` (kernel `decide` over the 16 tables), `tau_witness_three` (`x + y mod 3`), `sigma_witness_four` (table from `scripts/k2_search.py`), `tau_bij`, `sigma_bij`. Axioms: standard three.

## Sections 3–4 via Paper 1 (`Paper1Bridge.lean`)
| V6 | Lean (type abridged) | Hypotheses compared |
|---|---|---|
| `prop:flatten` (b) | `FiniteFlattening.solutionsEquiv Γ I : TypeEquiv (Solutions Γ I) {b // Holds Γ I b}`; `flatten_invFun_restrict : (…invFun b).1 = restrict b.1 := rfl`; `TermTheory.maxSolutionCount_eq_normalized` | every `A`, every `I`; V6's `Γ^nf` (equalities + depth-1 equations) is `FiniteFlattening.Holds` |
| `lem:quotient` | `TermSystem.explicitEqualitiesSolutionsEquiv Γ E I` | V6's chosen representatives are replaced by quotient classes |
| `lem:collision-quotient` | `TermSystem.collisionFreeSolutionsEquiv`, `collisionFreeSystem_noCollision` (closed relation `CollisionEqv`); one-pass version refuted by `onePassQuotient_not_leftFunctional` | see F-01 |
| `lem:div-easy` | `diversification_le [Fintype σ.Symbol] [Fintype Var] [Fintype A] : maxSolutionCount Γ ≤ maxSolutionCount (diversify Γ)` | every finite alphabet |
| `prop:solutions-winning` | `solutions_eq_winning (hfnf : OutputFunctional Γ) : maxSolutionCount (diversify Γ) = ordinaryWinningMax Γ` | V6's ordinary game with sources = `OrdinaryStrategy` (distinct in-neighbours, one rule per defined variable) |
| `thm:sandwich` | `sandwich_upper Γ n : maxSolutionCount (Fin n) Γ ≤ maxSolutionCount (Fin n) (diversify Γ)`; `sandwich_lower [Nonempty Var] (hΓ : NoCollision Γ) (hn : card Var ≤ n) : maxSolutionCount (Fin (n / card Var)) (diversify Γ) ≤ maxSolutionCount (Fin n) Γ` | V6 assumes CFNF; only collision-freeness is used; `v ≥ 1` |
| `cor:sandwich-asympt` | `sandwich_limsup (hΓ) (hfnf)` : the three `Filter.limsup`s coincide (from Paper 1's limits via `Tendsto.limsup_eq`) | CFNF as printed |
| remark "Why FNF?" (ii) | refuted by `fnfRemark_quotient_not_outputFunctional`; repair `fnfRemark_paper1_repair` | see F-02 |
| `def:instance-size` remark | `size_doublingTerm n : (doublingTerm n).size = 2 ^ (n + 1) - 1`, `card_subterms_doublingTerm n : (doublingTerm n).subterms.card = n + 1` | see F-08 |

## The routing lower bound (`Routing.lean`; source Definition 9 / Lemma 4)

*Source statement.* For `|A| > |Γ_sub|`, a "dynamic routing" interpretation
on the tagged alphabet realises at least `(|B|−1)^ρ` outputs, `ρ` the number
of routed paths.

*Lean.* `DirectChild`, `instanceSubterms` (`Γ_sub`), `DagPath` (a path in
the shared term DAG from an input variable to an output term; within-path
vertices are automatically distinct because a child has strictly smaller
size), `PathSystem t q` (pairwise vertex-disjoint family);
`routingInterpretation P m d : Interpretation σ (Sub t × Fin m)` — one total
table per symbol, reconstructing the current subterm from the argument tags
and forwarding the path predecessor's block value (this is how repeated
symbols are handled with a single table, exactly the source's mechanism);
`eval_routing : u.eval … = (u, routeBlock u)` for every subterm `u`
(structural induction);
`pathSystem_pow_le_dispN : m^q ≤ Disp_{s·m}(t)` (`s = |Sub t|`, `m ≥ 1`,
`r ≥ 1`) — the source's Lemma 4 in cardinal form;
`pathSystem_lowerBound_real : ∃ c > 0, ∃ N, ∀ n ≥ N, c·n^q ≤ Disp_n(t)`
(with `c = (2s)^{−q}`, `N = 2s`);
weak duality `pathSystem_card_le_of_termCut` / `pathSystem_card_le_termCutNumber`
(`q ≤ ρ(t)`: every path meets every term-cut, by descent along the path);
`MengerForTerms t := Nonempty (PathSystem t (termCutNumber t))`;
worked certificate: `singleEdgePath`, `diamondPathSystem` (the four
vertex-disjoint paths `x→f(x,y)`, `z→f(x,z)`, `y→f(y,w)`, `w→f(z,w)`),
`mengerForTerms_diamond`.
Axioms: standard three.
*Matching.* The construction covers arbitrary nested terms, repeated
arguments, constants (arity 0), shared subterms (tags are subterm
identities) and repeated symbols (one global table).  The source's
`|B| − 1` slack is absorbed into the constant.

## Section 7.1 — `σ` has no 3-element witness (`ExperimentsSigmaThree.lean`)

`tblDigit`/`sigmaOutN` (base-3 digit encoding of tables and packed
outputs), instance-free Bool recursions `collideWith`/`collideBelow`/
`allCollide` with specification lemmas, kernel evaluation
`sigma_all_tables_collide : allCollide 19683 = true` (`decide +kernel`),
encoding bridge `tblDigit_encodeTbl`, `sigmaOutN_encodeTbl`,
`termMap_sigmaPair`; result `sigma_no_witness_three` and the assembled
`sigma_bijectivity_spectrum_low` (no witness at 2 or 3; explicit witness at
4).  Axioms: standard three.

## Section 7.3 — second "consequently" clause (`ScalarLinear.lean`)

`modP p Δ` (reduction mod `p`), `aeval_int_eq_aeval_modP` (evaluation in a
`ZMod p`-algebra factors through the reduction),
`exists_eval_ne_zero_galoisField` (a nonzero polynomial over `𝔽_p` has a
nonzero value over `𝔽_{p^{D+2}}`, via `MvPolynomial.eq_zero_of_eval_eq_zero`),
`exists_galoisField_witness_iff [Fintype σ.Symbol] (t) (p) [Fact p.Prime] :
(∃ m > 0, ScalarLinearWitness t (GaloisField p m)) ↔ modP p (symbolicDet t) ≠ 0`.
Axioms: standard three.

## Conditional layer (`Conditional/MaxFlowExponent.lean`)
Hypothesis: `MaxFlowLowerBound t := ∃ c : ℝ, 0 < c ∧ ∃ N, ∀ n ≥ N, c * n ^ termCutNumber t ≤ dispN t n`.
`exponentData_of_lowerBound`, `exponent_eq_termCutNumber (hr : 0 < r) (h) : exponent t = termCutNumber t`, `threshold_iff_of_lowerBound`, `fullRate_iff_termCutNumber`, `fullRate_iff_eventual : FullRateDisp t ↔ ∃ N, ∀ n ≥ N, n ^ (r-1) + 1 ≤ dispN t n`, `perfect_implies_termCutNumber_eq`, `maxFlowLowerBound_diamond`. Unconditional: `exponent_le_termCutNumber`, `exponent_le_outputs`, `exponent_nonneg`, `one_le_dispN`.
Discharging the hypothesis: `maxFlowLowerBound_of_pathSystem (t) (hr) (P : PathSystem t (termCutNumber t)) : MaxFlowLowerBound t` and `maxFlowLowerBound_of_menger (t) (hr) (h : MengerForTerms t) : MaxFlowLowerBound t`.
Axioms: standard three (no project postulate).
