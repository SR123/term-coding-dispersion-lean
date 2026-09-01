import TermCoding.Normalisation
import TermCoding.FunctionalCompletion
import TermCoding.Sandwich
import TermCoding.SystemExponent
import TermCoding.OrdinaryGame
import TermCoding.Dispersion.Attacks
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# V6 Sections 2–4 versus the Paper 1 development

V6 restates, in simplified form, the preprocessing pipeline and the
guessing-number sandwich of Paper 1.  This file proves the *printed* V6
statements from the exact Paper 1 declarations (Lean-checked matches), and
records two places where the V6 prose does **not** match the checked
mathematics:

* `lem:collision-quotient` (one-pass collision relation) --
  `onePassQuotient_not_leftFunctional`: quotienting by the relation
  generated in one pass from the *original* left-hand collisions can create
  new collisions, so the printed conclusion "`Γ^cf` is collision-free" is
  false as stated.  Paper 1 uses the closed relation `CollisionEqv`
  (`collisionFreeSystem_noCollision`).
* Remark "Why FNF?", option (ii) -- `fnfRemark_quotient_not_outputFunctional`:
  splitting definitions, adding copy equalities and then *quotienting* them
  restores the multiple definitions, so the procedure does not produce FNF.
  Paper 1 keeps the copy equalities as explicit constraints
  (`completionSolutionsEquiv`).

Matches (all with Paper 1's own hypotheses):

| V6 | Lean |
|---|---|
| `prop:flatten` (b) | `FiniteFlattening.solutionsEquiv`, `flatten_invFun_restrict`; `TermTheory.maxSolutionCount_eq_normalized` |
| `lem:quotient` | `TermSystem.explicitEqualitiesSolutionsEquiv` |
| `lem:collision-quotient` (closed relation) | `TermSystem.collisionFreeSolutionsEquiv`, `collisionFreeSystem_noCollision` |
| `lem:div-easy` | `diversification_le` |
| `prop:solutions-winning` | `solutions_eq_winning` |
| `thm:sandwich` | `sandwich_upper`, `sandwich_lower` |
| `cor:sandwich-asympt` | `sandwich_limsup` |

Also here (it needs Paper 1's `Term.subterms`): `card_subterms_doublingTerm`,
the DAG-size half of the tree-versus-DAG size gap (`size_doublingTerm` in
`Attacks`).
-/

namespace TermCoding

namespace Dispersion

open Filter

universe uSym uVar uAlpha

/-! ### `prop:flatten` -/

/-- The inverse of the flattening bijection is restriction to the original
variables, as the manuscript states. -/
theorem flatten_invFun_restrict {σ : Signature.{uSym}} {Original : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermTheory σ Original m) (I : Interpretation σ A)
    (b : {b : Assignment (FiniteFlattening.Var Γ) A // FiniteFlattening.Holds Γ I b}) :
    ((FiniteFlattening.solutionsEquiv Γ I).invFun b).1 = FiniteFlattening.restrict b.1 := rfl

/-! ### `lem:div-easy` -/

/-- `S_n(Γ) ≤ S_n(Γ^div)` for every finite alphabet. -/
theorem diversification_le {σ : Signature.{uSym}} {Var : Type uVar} {A : Type uAlpha}
    {m : Nat} [Fintype σ.Symbol] [Fintype Var] [Fintype A] (Γ : TermSystem σ Var m) :
    TermSystem.maxSolutionCount (A := A) Γ ≤
      TermSystem.maxSolutionCount (A := A) (TermSystem.diversify Γ) := by
  rw [TermSystem.diversifiedMaxSolutionCount_eq_winningMax]
  exact TermSystem.maxSolutionCount_le_winningMax Γ

/-! ### `prop:solutions-winning` -/

/-- For an FNF instance, `S_n(Γ^div) = W(G_Γ, Src(Γ); n)`, the maximum
number of winning configurations of the ordinary guessing game on the
dependency digraph with sources (one local rule per defined variable,
seeing its distinct in-neighbours). -/
theorem solutions_eq_winning {σ : Signature.{uSym}} {Var : Type uVar} {A : Type uAlpha}
    {m : Nat} [Fintype Var] [Fintype A] (Γ : TermSystem σ Var m)
    (hfnf : TermSystem.OutputFunctional Γ) :
    TermSystem.maxSolutionCount (A := A) (TermSystem.diversify Γ) =
      TermSystem.ordinaryWinningMax (A := A) Γ :=
  TermSystem.diversifiedMaxSolutionCount_eq_ordinaryWinningMax_of_outputFunctional Γ hfnf

/-! ### `thm:sandwich` -/

/-- Upper bound: `S_n(Γ) ≤ S_n(Γ^div)` for every `n` (no hypothesis). -/
theorem sandwich_upper {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}
    [Fintype σ.Symbol] [Fintype Var] (Γ : TermSystem σ Var m) (n : Nat) :
    TermSystem.maxSolutionCount (A := Fin n) Γ ≤
      TermSystem.maxSolutionCount (A := Fin n) (TermSystem.diversify Γ) :=
  diversification_le Γ

/-- Lower bound: for a collision-free instance with `v` variables and every
`n ≥ v`, `S_n(Γ) ≥ S_{⌊n/v⌋}(Γ^div)`.  (V6 assumes CFNF; only the
collision-free half is needed.) -/
theorem sandwich_lower {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}
    [Fintype σ.Symbol] [Fintype Var] [Nonempty Var] (Γ : TermSystem σ Var m)
    (hΓ : TermSystem.NoCollision Γ) {n : Nat} (hn : Fintype.card Var ≤ n) :
    TermSystem.maxSolutionCount (A := Fin (n / Fintype.card Var)) (TermSystem.diversify Γ) ≤
      TermSystem.maxSolutionCount (A := Fin n) Γ := by
  rw [TermSystem.diversifiedMaxSolutionCount_eq_winningMax]
  exact (TermSystem.finiteSandwich_fintype hn Γ hΓ).1

/-! ### `cor:sandwich-asympt` -/

/-- The three `limsup` quantities of `cor:sandwich-asympt` coincide for a
collision-free FNF instance (V6: CFNF).  Paper 1 proves the stronger
statement that all three sequences converge to the same limit. -/
theorem sandwich_limsup {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}
    [Fintype σ.Symbol] [Fintype Var] [Nonempty Var] (Γ : TermSystem σ Var m)
    (hΓ : TermSystem.NoCollision Γ) (hfnf : TermSystem.OutputFunctional Γ) :
    limsup (TermSystem.maxSolutionRate Γ) atTop =
        limsup (TermSystem.diversifiedMaxSolutionRate Γ) atTop ∧
      limsup (TermSystem.diversifiedMaxSolutionRate Γ) atTop =
        limsup (fun n : Nat =>
          Real.log (TermSystem.ordinaryWinningMax (A := Fin n) Γ) / Real.log n) atTop := by
  have h1 := (TermSystem.maxSolutionRate_tendsto Γ hΓ).limsup_eq
  have h2 := (TermSystem.diversifiedMaxSolutionRate_tendsto Γ).limsup_eq
  have h3 : (fun n : Nat =>
      Real.log (TermSystem.ordinaryWinningMax (A := Fin n) Γ) / Real.log n) =
      TermSystem.diversifiedMaxSolutionRate Γ := by
    funext n
    unfold TermSystem.diversifiedMaxSolutionRate
    rw [solutions_eq_winning Γ hfnf]
  refine ⟨by rw [h1, h2], ?_⟩
  rw [h3]

/-! ### Counterexample: the one-pass collision relation of `lem:collision-quotient` -/

/-- The relation generated in one pass from the left-hand collisions present
in `Γ` itself (V6's `≈`). -/
def onePassCollisionGenerator {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}
    (Γ : TermSystem σ Var m) (v w : Var) : Prop :=
  ∃ i j, (Γ i).leftSide = (Γ j).leftSide ∧ (Γ i).output = v ∧ (Γ j).output = w

/-- V6's `≈` as a setoid. -/
def onePassSetoid {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}
    (Γ : TermSystem σ Var m) : Setoid Var :=
  Relation.EqvGen.setoid (onePassCollisionGenerator Γ)

/-- Two unary symbols `f, g`. -/
def twoUnarySignature : Signature where
  Symbol := Fin 2
  arity := fun _ => 1

/-- Variables `x = 0, v = 1, w = 2, a = 3, b = 4`; equations
`f(x) = v`, `f(x) = w`, `g(v) = a`, `g(w) = b`. -/
def onePassExample : TermSystem twoUnarySignature (Fin 5) 4 :=
  ![⟨(0 : Fin 2), fun _ => 0, 1⟩, ⟨(0 : Fin 2), fun _ => 0, 2⟩,
    ⟨(1 : Fin 2), fun _ => 1, 3⟩, ⟨(1 : Fin 2), fun _ => 2, 4⟩]

/-- The class function separating `{x}, {v,w}, {a}, {b}`. -/
def onePassClass : Fin 5 → Fin 4 := ![0, 1, 1, 2, 3]

/-- The generator relation respects the class function (exhaustive case
analysis over the `4 × 4` pairs of equations). -/
theorem onePassGenerator_class (i j : Fin 4)
    (hij : (onePassExample i).leftSide = (onePassExample j).leftSide) :
    onePassClass (onePassExample i).output = onePassClass (onePassExample j).output := by
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | (exfalso
       simp only [onePassExample, Equation.leftSide] at hij
       first
         | exact absurd (Sigma.ext_iff.mp hij).1 (by decide)
         | (have hargs := eq_of_heq (Sigma.ext_iff.mp hij).2
            have := congrFun hargs ⟨0, Nat.zero_lt_one⟩
            exact absurd this (by decide)))

theorem onePassClass_invariant {v w : Fin 5}
    (h : Relation.EqvGen (onePassCollisionGenerator onePassExample) v w) :
    onePassClass v = onePassClass w := by
  induction h with
  | rel v w hvw =>
      obtain ⟨i, j, hij, hi, hj⟩ := hvw
      subst hi
      subst hj
      exact onePassGenerator_class i j hij
  | refl v => rfl
  | symm v w _ ih => exact ih.symm
  | trans v w z _ _ ih1 ih2 => exact ih1.trans ih2

/-- In the one-pass quotient, `g([v]) = [a]` and `g([w]) = [b]` become a
left-hand collision with `[a] ≠ [b]`: the quotient is not collision-free
(`LeftFunctional` fails), contrary to the printed conclusion of
`lem:collision-quotient`. -/
theorem onePassQuotient_not_leftFunctional :
    ¬ TermSystem.LeftFunctional
      (TermSystem.variableQuotient onePassExample (onePassSetoid onePassExample)) := by
  intro h
  have hleft : (TermSystem.variableQuotient onePassExample (onePassSetoid onePassExample) 2).leftSide =
      (TermSystem.variableQuotient onePassExample (onePassSetoid onePassExample) 3).leftSide := by
    simp only [TermSystem.variableQuotient, Equation.leftSide, onePassExample]
    congr 1
    funext p
    apply Quotient.sound
    apply Relation.EqvGen.rel
    exact ⟨0, 1, rfl, rfl, rfl⟩
  have hout := h 2 3 hleft
  simp only [TermSystem.variableQuotient, onePassExample] at hout
  have := Quotient.exact hout
  have hinv := onePassClass_invariant this
  simp [onePassClass] at hinv

/-! ### Counterexample: the FNF remark's quotient -/

/-- One unary symbol. -/
def oneUnarySignature : Signature where
  Symbol := Unit
  arity := fun _ => 1

/-- `f(x) = v`, `f(y) = v` (variables `x = 0, y = 1, v = 2`): two defining
equations for `v`. -/
def fnfExample : TermSystem oneUnarySignature (Fin 3) 2 :=
  ![⟨(), fun _ => 0, 2⟩, ⟨(), fun _ => 1, 2⟩]

/-- The copy equalities `z_e = v` for each equation `e`, as in V6's option
(ii). -/
def fnfCopyEqualities : TermSystem.VariableEqualities (TermSystem.CompletionVar (Fin 3) 2) 2 :=
  fun i => (Sum.inr i, Sum.inl (fnfExample i).output)

/-- Splitting the definitions (Paper 1's `splitCore`), adding the copy
equalities and then quotienting by them (Paper 1's `variableQuotient` with
the generated setoid) re-identifies the two fresh outputs: the result is not
output-functional, so V6's option (ii) as printed does not yield FNF. -/
theorem fnfRemark_quotient_not_outputFunctional :
    ¬ TermSystem.OutputFunctional
      (TermSystem.variableQuotient (TermSystem.splitCore fnfExample)
        (TermSystem.equalitySetoid fnfCopyEqualities)) := by
  intro h
  have h01 : (TermSystem.variableQuotient (TermSystem.splitCore fnfExample)
      (TermSystem.equalitySetoid fnfCopyEqualities) 0).output =
      (TermSystem.variableQuotient (TermSystem.splitCore fnfExample)
      (TermSystem.equalitySetoid fnfCopyEqualities) 1).output := by
    simp only [TermSystem.variableQuotient, TermSystem.splitCore]
    apply Quotient.sound
    have h0 : Relation.EqvGen (TermSystem.equalityGenerator fnfCopyEqualities)
        (Sum.inr (0 : Fin 2)) (Sum.inl (2 : Fin 3)) :=
      Relation.EqvGen.rel _ _ ⟨0, rfl⟩
    have h1 : Relation.EqvGen (TermSystem.equalityGenerator fnfCopyEqualities)
        (Sum.inr (1 : Fin 2)) (Sum.inl (2 : Fin 3)) :=
      Relation.EqvGen.rel _ _ ⟨1, rfl⟩
    exact Relation.EqvGen.trans _ _ _ h0 (Relation.EqvGen.symm _ _ h1)
  have := h 0 1 h01
  exact absurd this (by decide)

/-- By contrast, Paper 1's functional completion keeps the copy equalities
explicit: the split core *is* output-functional and the solution count is
preserved exactly. -/
theorem fnfRemark_paper1_repair :
    TermSystem.OutputFunctional (TermSystem.splitCore fnfExample) ∧
      ∀ (A : Type) (I : Interpretation oneUnarySignature A),
        Nat.card (TermSystem.CompletionSolutions fnfExample I) =
          Nat.card (TermSystem.Solutions fnfExample I) :=
  ⟨TermSystem.splitCore_outputFunctional fnfExample,
    fun _ I => TermSystem.completionSolutionCard_eq fnfExample I⟩

/-! ### Tree size versus DAG size -/

/-- Every subterm of `t` has size at most the size of `t`. -/
theorem Term.size_le_of_mem_subterms {σ : Signature.{uSym}} {V : Type uVar} :
    ∀ t : Term σ V, ∀ u ∈ t.subterms, u.size ≤ t.size
  | .var v, u, hu => by
      rw [Term.subterms_var, Finset.mem_singleton] at hu
      subst hu
      exact le_rfl
  | .app s args, u, hu => by
      classical
      rw [Term.subterms_app, Finset.mem_insert, Finset.mem_biUnion] at hu
      rcases hu with rfl | ⟨p, _, hp⟩
      · exact le_rfl
      · have h1 := Term.size_le_of_mem_subterms (args p) u hp
        have h2 : (args p).size ≤ (Term.app s args).size := by
          simp only [Term.size]
          have := Finset.single_le_sum (f := fun q => (args q).size)
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)
          simp only at this
          omega
        exact h1.trans h2

/-- The shared term DAG of `doublingTerm n` has exactly `n + 1` nodes, while
its syntax tree has `2^{n+1} − 1` nodes (`size_doublingTerm`): the two size
measures are not polynomially related. -/
theorem card_subterms_doublingTerm (n : Nat) : (doublingTerm n).subterms.card = n + 1 := by
  classical
  induction n with
  | zero =>
      show (Term.var (0 : Fin 1) : Term diamondSignature (Fin 1)).subterms.card = 1
      rw [Term.subterms_var]
      simp
  | succ n ih =>
      have hsub : (doublingTerm (n + 1)).subterms =
          insert (doublingTerm (n + 1)) (doublingTerm n).subterms := by
        show (fapp (doublingTerm n) (doublingTerm n)).subterms = _
        unfold fapp
        rw [Term.subterms_app]
        have hbi : (Finset.univ.biUnion fun p : Fin 2 =>
            (![doublingTerm n, doublingTerm n] p).subterms) = (doublingTerm n).subterms := by
          ext u
          simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨p, hp⟩
            fin_cases p <;> exact hp
          · intro hu
            exact ⟨0, hu⟩
        convert congrArg (insert (fapp (doublingTerm n) (doublingTerm n))) hbi using 2
      rw [hsub, Finset.card_insert_of_notMem, ih]
      intro hmem
      have h1 := Term.size_le_of_mem_subterms (doublingTerm n) _ hmem
      rw [size_doublingTerm, size_doublingTerm] at h1
      have h2 : 2 ^ (n + 1) < 2 ^ (n + 1 + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      have h3 : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
      omega

end Dispersion

end TermCoding
