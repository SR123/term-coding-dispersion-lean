# TermCodingDispersionLean — Lean 4 companion to *Term Coding and Dispersion: Exact and Asymptotic Decision Problems* (Paper 2, V11, 1 September 2026)

This repository contains a Lean 4 formalisation of the mathematical content
of the corrected Paper 2 manuscript, built on top of the released Paper 1
development (`TermCoding`, reused verbatim).  This is the release
candidate for the public repository accompanying the paper; the archival
DOI is minted via Zenodo on the first GitHub release.

* Lean `4.26.0`, Mathlib `v4.26.0` (commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`),
  pinned in `lean-toolchain` / `lake-manifest.json` (unchanged from Paper 1).
* Reused Paper 1 release: `github.com/SR123/term-coding-lean`, commit
  `d5592abeec515802c385ac99d1459c84fdf8b21c`; its tracked sources
  (`TermCoding/**`, `TermCoding.lean`, `scripts/NamespaceAxiomAudit.lean`,
  `LICENSE`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`) were
  copied byte-for-byte.  The Paper 2 modules live under
  `TermCoding/Dispersion/`.  `lakefile.toml`, `AxiomsAudit.lean`,
  `scripts/NamespaceAxiomAudit.lean` and this README were extended.
* No `sorry`, `admit`, project `axiom`, `opaque` proof, `unsafe`, or native
  evaluation.  Every constant in the `TermCoding` namespace depends only on
  `propext`, `Classical.choice`, `Quot.sound` (namespace-wide audit).

## Two roots

| Root | Content |
|---|---|
| `TermCodingDispersionVerified.lean` | unconditional, kernel-checked results (nothing depends on the 2019 max-flow theorem) |
| `TermCodingDispersionConditional.lean` | theorems whose statements carry the external input `MaxFlowLowerBound` as an explicit hypothesis |
| `TermCodingDispersion.lean` | both |

## What is formalised (Lean-checked)

Notation: `t : Instance σ k r` is a tuple of `r` output terms in `k` input
variables; `dispN t n = Disp_n(t)`; `exponent t = D(t)`; `termCutNumber t =
ρ(t)`, the min term-cut of Riis–Gadouleau (2019).

| V6 label | Lean declaration(s) |
|---|---|
| `def:dispersion-multisorted`, `def:decision-problems`, `def:bij3`, `def:instance-size` | `Dispersion.Instance`, `termMap`, `disp`, `dispN`, `PerfectDispAt`, `PerfectDisp`, `SurjectiveWitness`, `BIJ`, `FullRateDisp`, `Term.size`, `Instance.size` |
| `lem:diamond-not-bij` | `diamond_not_injective`, `diamond_not_surjective`, `diamond_not_perfect` |
| remark "diversification removes the obstruction" | `diversifiedDiamond_bijective` |
| `lem:disp-embed` | `dispN_eq_codingTheoryMax` (from Paper 1's `Examples.Dispersion.codingTheoryMax_eq_dispersionMax`); `disp_eq_dispersionMax`, `termMap_eq_paper1` are the exact matches |
| `lem:square-perfect-equals-bij` | `perfectDisp_iff_bij`, `surjectiveWitness_iff_bij`, `square_tfae` |
| `cor:bij-reduces-perfect` | `identity_reduction` (`ManyOneReduction`, size-preserving) |
| `rem:inverse-extension` | `bijective_of_inverseEquations`, `exists_inverseExtension_of_bijective`, `exists_inverseExtension_iff` |
| `lem:product-surjectivity`, `lem:direct-power` | `eval_productInterp`, `termMap_productInterp`, `surjective_productInterp`, `dispN_mul_eq_of_perfect`; `eval_powerInterp`, `termMap_powerInterp_eq` (conjugation by `Equiv.piComm`), `surjective_powerInterp`, `dispN_pow_eq_of_perfect` |
| `def:perfect-spectrum`, `thm:perfect-spectrum-structure` | `perfectSpectrum`, `perfectSpectrum_nonempty_iff`, `mul_mem_perfectSpectrum` (i), `pow_mem_perfectSpectrum`, `exponent_eq_of_spectrum_nonempty` (ii), `exponent_diamond` + `lem:diamond-not-bij` names (iii); square membership bridge `mem_perfectSpectrum_square_iff` |
| `thm:perfect-implies-full-rate` | `exponent_eq_of_perfect`, `fullRateDisp_of_perfectDisp` (**unconditional**: the limit `D(t)` exists by Paper 1's sandwich theorem, `dispRate_tendsto`); converse: `exponent_diamond`, `not_perfect_of_fullRate_fails` |
| `lem:padding-outputs`, `lem:unused-inputs` | `padMap_surjective_iff`, `restrictMap_surjective_iff` (with `Nonempty A`; the degenerate failure without it: `padMap_not_surjective_empty`) |
| `thm:reduction-kk`, `thm:reduction-nr` | transformer `padInstance`; `termMap_padInstance`, `perfectDisp_padInstance_iff`, `size_padInstance` (`‖pad p‖ + 2k₀ = ‖p‖ + 2r`), `reduction_kk`, `reduction_nr`, `decidable_bij3_of_decidable_perfect` |
| `rem:k-less-r` | `disp_lt_pow_of_lt` |
| `thm:one-output`, `cor:bij-one`, `thm:landscape`(ii) | `prescription_consistent`, `routingInterp`, `eval_routingInterp_slice`, `perfectDisp_single_iff`, `mem_perfectSpectrum_single_iff`, `perfectSpectrum_single_of_hasVar`, `perfectSpectrum_single_of_ground`, `perfectSpectrum_single_dichotomy`, `bij_one_iff`, `bijective_single_of_hasVar` |
| remark "The borderline output dimension `r = 2`" | `perfectDisp_two_iff_bij_two` (the square subfamily of `Perfect-Disp_2` is `BIJ_2`) |
| `thm:ptime-threshold` (analytic layer) | `ExponentData`, `ThresholdConditions`, `threshold_iff`, `decideThreshold_correct`, `rate_tendsto`, `thresholdConditions_pow_add_one` |
| `thm:ptime-threshold` (for term dispersion) | conditional: `threshold_iff_of_lowerBound` |
| `thm:disp-exponent`, uniform upper bound | `ExprFrom`, `IsTermCut`, `termCutNumber`, `imageCard_le_pow_card_of_termCut`, `disp_le_pow_termCutNumber`, `dispN_le_pow_termCutNumber` (this is Lemma 3 of the 2019 source) |
| `thm:disp-exponent`, integrality / `Θ` / limit | conditional: `MaxFlowLowerBound`, `exponentData_of_lowerBound`, `exponent_eq_termCutNumber`; unconditional bounds `exponent_le_termCutNumber`, `exponent_le_outputs`, `exponent_nonneg` |
| `thm:disp-exponent`, lower-bound construction (source Def. 9 / Lemma 4) | **`Routing.lean` (kernel-checked)**: `DagPath`, `PathSystem`, `routingInterpretation`, `eval_routing`, `pathSystem_pow_le_dispN` (`m^q ≤ Disp_{s·m}`), `pathSystem_lowerBound_real` (`Θ`-form), weak duality `pathSystem_card_le_termCutNumber`; hence `maxFlowLowerBound_of_pathSystem` / `maxFlowLowerBound_of_menger` — the external input shrinks to Menger's theorem for the term DAG (`MengerForTerms`) |
| `lem:diamond-maxflow` (in the source's term-cut model) | `termCutNumber_diamond` (`ρ = 4`), `exponentData_diamond`, `maxFlowLowerBound_diamond`; explicit flow certificate `diamondPathSystem`, `mengerForTerms_diamond` |
| `cor:full-rate-ptime`, `Full-Rate-Disp` | conditional: `fullRate_iff_termCutNumber`, `fullRate_iff_eventual` (mathematical content only) |
| `thm:landscape` (i)–(iii) | `landscape_square`, `landscape_reduction`, `landscape_rate` |
| `prop:scalar-det-criterion-main` | `coeff`, `symbolicMatrix`, `symbolicDet`, `eval_scalarLinearInterp`, `termMap_scalarLinear`, `bijective_scalarLinear_iff`, `scalarLinearWitness_iff`; consequences: `scalarLinearWitness_decidable` (finite field), `exists_galoisField_witness_iff` (second clause: extensions of a fixed `𝔽_p`), `exists_primeField_witness_iff` (prime-field form of the third clause), `exists_finiteField_witness_iff` (literal "some finite field" form of clause (c)) |
| `prop:small-spectra` | kernel checks: `tau_no_witness_two`, `sigma_no_witness_two`, `tau_witness_three`, `sigma_witness_four` (`decide`); `sigma_no_witness_three` (all `3^9` tables, instance-free Bool recursion, `decide +kernel`), `sigma_bijectivity_spectrum_low`; spectrum form: `perfectSpectrum_tau_least`, `perfectSpectrum_sigma_least` (least elements `3` and `4`), `pow_three_mem_perfectSpectrum_tau`, `pow_four_mem_perfectSpectrum_sigma` |
| `prop:flatten`, `lem:quotient`, `lem:collision-quotient`, `lem:div-easy`, `prop:solutions-winning`, `thm:sandwich`, `cor:sandwich-asympt` | Paper 1 declarations, restated in V6's form in `Paper1Bridge.lean` (`flatten_invFun_restrict`, `diversification_le`, `solutions_eq_winning`, `sandwich_upper`, `sandwich_lower`, `sandwich_limsup`) |

Reused Paper 1 declarations (all unchanged): `Signature`, `Term`, `Term.eval`,
`Interpretation`, `Assignment`, `TermEquation`, `TermTheory`,
`TermTheory.Solutions`, `TermTheory.solutionCount`, `TermTheory.maxSolutionCount`,
`TermTheory.maxSolutionRate`, `TermTheory.exponent`, `TermTheory.maxSolutionRate_tendsto`,
`TermTheory.maxSolutionCount_eq_normalized`, `FiniteFlattening.solutionsEquiv`,
`FiniteFlattening.restrict`, `Normalisation.system`, `Normalisation.solutionsEquiv`,
`Normalisation.system_noCollision`, `TermSystem.variableQuotient`,
`TermSystem.equalitySetoid`, `TermSystem.explicitEqualitiesSolutionsEquiv`,
`TermSystem.CollisionEqv`, `TermSystem.collisionFreeSolutionsEquiv`,
`TermSystem.collisionFreeSystem_noCollision`, `TermSystem.LeftFunctional`,
`TermSystem.NoCollision`, `TermSystem.OutputFunctional`, `TermSystem.splitCore`,
`TermSystem.completionSolutionsEquiv`, `TermSystem.completionSolutionCard_eq`,
`TermSystem.diversify`, `TermSystem.maxSolutionCount`,
`TermSystem.maxSolutionCount_le_winningMax`, `TermSystem.diversifiedMaxSolutionCount_eq_winningMax`,
`TermSystem.diversifiedMaxSolutionCount_eq_ordinaryWinningMax_of_outputFunctional`,
`TermSystem.ordinaryWinningMax`, `TermSystem.finiteSandwich_fintype`,
`TermSystem.maxSolutionRate`, `TermSystem.maxSolutionRate_tendsto`,
`TermSystem.diversifiedMaxSolutionRate`, `TermSystem.diversifiedMaxSolutionRate_tendsto`,
`Term.subterms` (+ `subterms_var`, `subterms_app`), `Examples.Dispersion.termMap`,
`Examples.Dispersion.ImagePoints`, `Examples.Dispersion.dispersionMax`,
`Examples.Dispersion.codingSignature`, `Examples.Dispersion.CodingVar`,
`Examples.Dispersion.codingTheory`, `Examples.Dispersion.codingTheoryMax_eq_dispersionMax`.

## What is *not* formalised

1. **Menger's theorem for the term DAG** (`MengerForTerms t`): the existence
   of `ρ(t)` pairwise vertex-disjoint variable-to-output paths.  This is now
   the *only* external mathematical input for `thm:disp-exponent`: the
   source's routing construction (Definition 9 / Lemma 4) and its upper
   bound (Lemma 3) are both kernel-checked (`Routing.lean`, `TermCut.lean`),
   and `maxFlowLowerBound_of_menger` derives the `Θ` lower bound
   `MaxFlowLowerBound t` from it.  Weak duality (`q ≤ ρ(t)`) is also
   checked, so `MengerForTerms` is exactly the min-cut = max-flow equality.
   For a concrete instance it can be discharged by exhibiting the paths
   (`diamondPathSystem`, `mengerForTerms_diamond`).  The conditional layer
   is unchanged: every asymptotic consequence carries `MaxFlowLowerBound t`
   (or, equivalently now, `MengerForTerms t`) as an explicit hypothesis.
2. **Polynomial-time claims** (computability of `ρ(t)`/`D(t)` by max-flow,
   `cor:full-rate-ptime`, the "polynomial time" clause of
   `thm:ptime-threshold`, "polynomial-time many-one reduction").  Lean has no
   cost model.  The syntactic transformers are structurally recursive
   computable functions with proved linear size bounds; the decision rule
   `decideThreshold` is proved correct; the computation of `ρ(t)` is a
   min vertex-cut in the term DAG (standard, external).
3. **Matrix-linear witnesses** (Section 7.3, noncommutative rank): not
   formalised, classified as literature.
4. **Open-status statements** (`prob:bij3-open`, `rem:bij-status-brief`,
   Section 7): outside the verified layer by nature.
5. The `k = 2` *spectrum* claims of Section 7.1 (e.g. "all sizes except 2"
   for `τ`, "all perfect squares" for `σ`) beyond the kernel-checked cases:
   sizes `2, 3, 4` are now fully checked for `σ` and sizes `2, 3` for `τ`.

## Findings recorded during formalisation

See `docs/PROOF_MAP.md` and the audit reports.  In brief: the one-pass
collision relation of `lem:collision-quotient` does not yield a collision-free
instance (`onePassQuotient_not_leftFunctional`); option (ii) of the remark
"Why FNF?" does not yield FNF (`fnfRemark_quotient_not_outputFunctional`);
tree size and DAG size are not polynomially related
(`size_doublingTerm`, `card_subterms_doublingTerm`); the network outline
(N1)–(N4) does not describe the 2019 construction (its cut is a syntactic
term-cut with unit capacity on *every* subterm including the input
variables, and no coupling gadgets); `lem:padding-outputs` needs a nonempty
alphabet when `k > r`.

## Build and check

```bash
lake exe cache get
lake build
lake env lean scripts/NamespaceAxiomAudit.lean
lake env lean AxiomsAudit.lean
rg -n '\b(sorry|admit|axiom|opaque)\b' TermCoding --glob '*.lean'   # must print nothing
```

The only resource-relaxing option in the tree is
`set_option maxHeartbeats 1000000` in the reused Paper 1 file
`TermCoding/Examples/DispersionTermCoding.lean` (plus one linter silencer,
`linter.unusedSimpArgs false`, on `diamondPathSystem`).

## Layout

```
TermCoding/Dispersion/Basic.lean              instances, Θ^I, Disp, decision problems, transport
TermCoding/Dispersion/Diamond.lean            lem:diamond-not-bij, routing lower bound
TermCoding/Dispersion/SquareBijectivity.lean  lem:square-perfect-equals-bij, cor:bij-reduces-perfect, rem:inverse-extension
TermCoding/Dispersion/DirectPower.lean        lem:direct-power
TermCoding/Dispersion/Padding.lean            lem:padding-outputs, lem:unused-inputs
TermCoding/Dispersion/Reductions.lean         thm:reduction-kk, thm:reduction-nr (syntax transformer + size)
TermCoding/Dispersion/OneOutput.lean          one-output construction, BIJ_1
TermCoding/Dispersion/Spectrum.lean           perfect-alphabet spectrum (V10)
TermCoding/Dispersion/SmallSpectra.lean       least-alphabet results (V10)
TermCoding/Dispersion/SpectrumExponent.lean   spectrum => full rate (V10)
TermCoding/Dispersion/TermCut.lean            2019 Definition 2, Lemma 3; ρ(diamond) = 4
TermCoding/Dispersion/Routing.lean            2019 Definition 9, Lemma 4: paths, routing, Θ lower bound, weak duality
TermCoding/Dispersion/Threshold.lean          thm:ptime-threshold, analytic layer
TermCoding/Dispersion/ScalarLinear.lean       prop:scalar-det-criterion-main
TermCoding/Dispersion/Exponent.lean           D(t) as a limit (via Paper 1), perfect ⇒ full rate, D(diamond) = 4
TermCoding/Dispersion/Paper1Bridge.lean       V6 §§3–4 from Paper 1; two counterexamples; size gap
TermCoding/Dispersion/Attacks.lean            degenerate parameters
TermCoding/Dispersion/Experiments.lean        k = 2 kernel checks (sizes 2, 3-witness, 4-witness)
TermCoding/Dispersion/ExperimentsSigmaThree.lean   σ has no 3-element witness (19683 tables, kernel)
TermCoding/Dispersion/Landscape.lean          thm:landscape (i)–(iii)
TermCoding/Dispersion/Conditional/MaxFlowExponent.lean   explicit-hypothesis layer
```

## Licence

Apache-2.0 (as Paper 1).  The mathematics is the author's.  The corrected
V6 Lean development was produced and audited by Claude (Anthropic) on
30 August 2026; the V10 product-spectrum extension and the
independent-audit spectrum layer (Spectrum, SmallSpectra, SpectrumExponent,
and the finite-field witness form) were added on 31 August 2026.  The complete project is machine-checked.
