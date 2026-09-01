import TermCoding.Dispersion.Basic
import TermCoding.Dispersion.Diamond
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Fintype.Pi

/-!
# Term-cuts (Riis–Gadouleau 2019, Definition 2) and the cut upper bound

The primary source for `thm:disp-exponent` is

> S. Riis, M. Gadouleau, *Max-flow min-cut theorems on dispersion and
> entropy measures for communication networks*, Information and Computation
> 267 (2019) 49–73 (arXiv:1012.5224).

Its "network" is purely syntactic: Definition 2 there says that subterms
`s_1, …, s_ρ` *provide a term-cut of size `ρ`* for a term set `Γ` if every
term of `Γ` can be expressed syntactically by applying function symbols to
`s_1, …, s_ρ`; the *min-cut* of `Γ` is the minimum size of a term-cut.
Variables are subterms and count as cut elements of size one; there are no
"coupling gadgets" for repeated symbols in the source (symbol reuse is
handled inside its lower-bound construction by a tagged alphabet).

This file formalises that definition exactly and proves the source's
Lemma 3 (the uniform upper bound `Disp_n(t) ≤ n^ρ`) in Lean:

* `ExprFrom C u` -- `u` is expressible by applying function symbols to
  elements of `C` (constants are expressible for free).
* `IsTermCut t C` -- every output term is expressible from `C`.
* `imageCard_le_pow_card_of_termCut` -- `|Im Θ^I| ≤ |A|^{|C|}` for every
  interpretation and every term-cut `C` (Lemma 3 of the source).
* `termCutNumber t` -- the min-cut `ρ(t)`; `disp_le_pow_termCutNumber` --
  `Disp_A(t) ≤ |A|^{ρ(t)}` for every finite alphabet.
* `termCutNumber_diamond` -- the diamond's min-cut is `4`
  (`lem:diamond-maxflow` in the source's own model).  The lower bound `≥ 4`
  is derived from the explicit routing interpretation of
  `TermCoding.Dispersion.Diamond`, not from a flow diagram.

The lower half of the source's Theorem 1 (`Disp_n(t) ≥ (⌊n/|Γ_sub|⌋ − 1)^ρ`,
hence `Θ(n^ρ)`) is *not* formalised here; it enters only as an explicit
hypothesis in `TermCoding.Dispersion.Conditional.MaxFlowExponent`.
-/

namespace TermCoding

namespace Dispersion

universe uSym uAlpha

variable {σ : Signature.{uSym}} {k r : Nat}

/-- Syntactic expressibility from a set of terms by applying function
symbols (Riis–Gadouleau 2019, Definition 2). -/
inductive ExprFrom (C : Set (Term σ (Fin k))) : Term σ (Fin k) → Prop
  | mem {u : Term σ (Fin k)} (h : u ∈ C) : ExprFrom C u
  | app (s : σ.Symbol) (args : Fin (σ.arity s) → Term σ (Fin k))
      (h : ∀ p, ExprFrom C (args p)) : ExprFrom C (.app s args)

/-- A variable is expressible only if it is itself a cut element. -/
theorem ExprFrom.var_mem {C : Set (Term σ (Fin k))} {x : Fin k}
    (h : ExprFrom C (.var x)) : (Term.var x : Term σ (Fin k)) ∈ C := by
  cases h with
  | mem h => exact h

/-- Inversion for applications. -/
theorem ExprFrom.app_inv {C : Set (Term σ (Fin k))} {s : σ.Symbol}
    {args : Fin (σ.arity s) → Term σ (Fin k)} (h : ExprFrom C (.app s args)) :
    (Term.app s args ∈ C) ∨ ∀ p, ExprFrom C (args p) := by
  cases h with
  | mem h => exact Or.inl h
  | app _ _ h => exact Or.inr h

/-- Every term is expressible from the set of all variables. -/
theorem ExprFrom.of_vars (C : Set (Term σ (Fin k))) (hC : ∀ x, Term.var x ∈ C) :
    ∀ u : Term σ (Fin k), ExprFrom C u
  | .var x => ExprFrom.mem (hC x)
  | .app s args => ExprFrom.app s args (fun p => ExprFrom.of_vars C hC (args p))

/-- `C` is a term-cut for `t`: every output term is expressible from `C`. -/
def IsTermCut (t : Instance σ k r) (C : Finset (Term σ (Fin k))) : Prop :=
  ∀ i, ExprFrom (↑C) (t i)

section CutEval

variable {A : Type uAlpha} [Nonempty A]

/-- Evaluate a term "through the cut": read the value of a cut element from
`v`, and apply the interpretation to non-cut applications.  (`default` is
never reached on expressible terms.) -/
noncomputable def cutEval (I : Interpretation σ A) (C : Finset (Term σ (Fin k)))
    (v : C → A) : Term σ (Fin k) → A
  | .var x => by
      classical
      exact if h : (Term.var x : Term σ (Fin k)) ∈ C then v ⟨_, h⟩
        else Classical.choice inferInstance
  | .app s args => by
      classical
      exact if h : (Term.app s args : Term σ (Fin k)) ∈ C then v ⟨_, h⟩
        else I s (fun p => cutEval I C v (args p))

/-- The values of the cut elements under an assignment. -/
def cutValues (I : Interpretation σ A) (C : Finset (Term σ (Fin k)))
    (x : Fin k → A) : C → A :=
  fun c => c.1.eval I x

/-- On expressible terms, evaluation through the cut agrees with ordinary
evaluation when the cut values are the true values. -/
theorem cutEval_eq_eval (I : Interpretation σ A) (C : Finset (Term σ (Fin k)))
    (x : Fin k → A) {u : Term σ (Fin k)} (h : ExprFrom (↑C) u) :
    cutEval I C (cutValues I C x) u = u.eval I x := by
  classical
  induction h with
  | mem h =>
      rename_i u
      have h' : u ∈ C := Finset.mem_coe.mp h
      cases u with
      | var y =>
          simp only [cutEval]
          rw [dif_pos h']
          rfl
      | app s args =>
          simp only [cutEval]
          rw [dif_pos h']
          rfl
  | app s args _ ih =>
      simp only [cutEval]
      by_cases hmem : (Term.app s args : Term σ (Fin k)) ∈ C
      · rw [dif_pos hmem]
        rfl
      · rw [dif_neg hmem]
        simp only [Term.eval]
        congr 1
        funext p
        exact ih p

/-- Lemma 3 of the source: for every interpretation the term map factors
through the cut values, so its image has at most `|A|^{|C|}` elements. -/
theorem imageCard_le_pow_card_of_termCut [Fintype A] (t : Instance σ k r)
    (C : Finset (Term σ (Fin k))) (hC : IsTermCut t C) (I : Interpretation σ A) :
    imageCard t I ≤ Fintype.card A ^ C.card := by
  classical
  let G : (C → A) → (Fin r → A) := fun v i => cutEval I C v (t i)
  have hfactor : ∀ x, termMap t I x = G (cutValues I C x) := by
    intro x
    funext i
    exact (cutEval_eq_eval I C x (hC i)).symm
  have hsub : Set.range (termMap t I) ⊆ Set.range G := by
    rintro _ ⟨x, rfl⟩
    exact ⟨cutValues I C x, (hfactor x).symm⟩
  unfold imageCard
  calc Nat.card (Set.range (termMap t I))
      ≤ Nat.card (Set.range G) := Nat.card_mono (Set.toFinite _) hsub
    _ ≤ Nat.card (C → A) := Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
    _ = Fintype.card A ^ C.card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_coe]

end CutEval

/-- The set of sizes of term-cuts of `t`. -/
def termCutSizes (t : Instance σ k r) : Set Nat :=
  {ρ | ∃ C : Finset (Term σ (Fin k)), IsTermCut t C ∧ C.card = ρ}

/-- The variables form a term-cut of size `k`. -/
theorem variablesCut_isTermCut (t : Instance σ k r) :
    IsTermCut t (by classical exact Finset.univ.image (Term.var : Fin k → Term σ (Fin k))) := by
  classical
  intro i
  apply ExprFrom.of_vars
  intro x
  simp

/-- The output terms form a term-cut of size at most `r`. -/
theorem outputsCut_isTermCut (t : Instance σ k r) :
    IsTermCut t (by classical exact Finset.univ.image t) := by
  classical
  intro i
  apply ExprFrom.mem
  simp

theorem termCutSizes_nonempty (t : Instance σ k r) : (termCutSizes t).Nonempty := by
  classical
  exact ⟨_, Finset.univ.image (Term.var : Fin k → Term σ (Fin k)),
    variablesCut_isTermCut t, rfl⟩

/-- The min-cut `ρ(t)` of Riis–Gadouleau 2019: the least size of a term-cut. -/
noncomputable def termCutNumber (t : Instance σ k r) : Nat := sInf (termCutSizes t)

theorem exists_termCut_card_eq (t : Instance σ k r) :
    ∃ C : Finset (Term σ (Fin k)), IsTermCut t C ∧ C.card = termCutNumber t :=
  Nat.sInf_mem (termCutSizes_nonempty t)

theorem termCutNumber_le_of_termCut (t : Instance σ k r)
    (C : Finset (Term σ (Fin k))) (hC : IsTermCut t C) : termCutNumber t ≤ C.card :=
  Nat.sInf_le ⟨C, hC, rfl⟩

/-- `ρ(t) ≤ k` ("the min-cut is no more than the number of variables"). -/
theorem termCutNumber_le_inputs (t : Instance σ k r) : termCutNumber t ≤ k := by
  classical
  refine (termCutNumber_le_of_termCut t _ (variablesCut_isTermCut t)).trans ?_
  simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin k)))
    (f := (Term.var : Fin k → Term σ (Fin k)))

/-- `ρ(t) ≤ r` ("the min-cut is no more than the number of terms"). -/
theorem termCutNumber_le_outputs (t : Instance σ k r) : termCutNumber t ≤ r := by
  classical
  refine (termCutNumber_le_of_termCut t _ (outputsCut_isTermCut t)).trans ?_
  simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin r))) (f := t)

/-- The uniform cut bound `Disp_A(t) ≤ |A|^{ρ(t)}` on every finite alphabet
(the "in particular" clause of `thm:disp-exponent`, with `D(t)` read as the
source's min-cut). -/
theorem disp_le_pow_termCutNumber [Fintype σ.Symbol] {A : Type uAlpha} [Fintype A]
    [Nonempty A] (t : Instance σ k r) :
    disp A t ≤ Fintype.card A ^ termCutNumber t := by
  obtain ⟨C, hC, hcard⟩ := exists_termCut_card_eq t
  rw [← hcard]
  exact Finset.sup_le (fun I _ => imageCard_le_pow_card_of_termCut t C hC I)

/-- Numerical form `Disp_n(t) ≤ n^{ρ(t)}` for every `n ≥ 1` (and trivially
for `n = 0` when `k ≥ 1`). -/
theorem dispN_le_pow_termCutNumber [Fintype σ.Symbol] (t : Instance σ k r)
    {n : Nat} (hn : 1 ≤ n) : dispN t n ≤ n ^ termCutNumber t := by
  haveI : NeZero n := ⟨by omega⟩
  simpa using (disp_le_pow_termCutNumber (A := Fin n) t)

/-! ### The diamond gadget has min-cut `4` -/

/-- `lem:diamond-maxflow` in the source's model: the minimum term-cut of the
diamond has size `4`.  Upper bound: the four variables.  Lower bound: a cut
of size `≤ 3` would force `Disp_n ≤ n^3` for all `n`, contradicting the
explicit routing interpretation `Disp_{4m}(diamond) ≥ m^4` at `m = 65`. -/
theorem termCutNumber_diamond : termCutNumber diamond = 4 := by
  apply le_antisymm (termCutNumber_le_inputs diamond)
  by_contra hlt
  push_neg at hlt
  have h1 : dispN diamond 260 ≤ 260 ^ termCutNumber diamond :=
    dispN_le_pow_termCutNumber diamond (by norm_num)
  have h2 : 260 ^ termCutNumber diamond ≤ 260 ^ 3 :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3 : 65 ^ 4 ≤ dispN diamond (4 * 65) := pow_le_dispN_diamond 65
  norm_num at h3
  omega

end Dispersion

end TermCoding
