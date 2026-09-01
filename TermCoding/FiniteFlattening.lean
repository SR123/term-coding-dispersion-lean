import Mathlib
import TermCoding.Terms
import TermCoding.VariableQuotient

namespace TermCoding

universe uSym uVar uAlpha

namespace Term

noncomputable local instance termDecidableEq
    {σ : Signature.{uSym}} {Var : Type uVar} :
    DecidableEq (Term σ Var) := Classical.decEq _

/-- Computable subterm enumeration once equality of terms is supplied. -/
private def subtermsWith {σ : Signature.{uSym}} {Var : Type uVar}
    [DecidableEq (Term σ Var)] : Term σ Var → Finset (Term σ Var)
  | .var v => {Term.var v}
  | .app s args =>
      insert (Term.app s args)
        (Finset.univ.biUnion (fun p => subtermsWith (args p)))

/-- The finite set of syntactic subterms of a term. -/
noncomputable def subterms {σ : Signature.{uSym}} {Var : Type uVar}
    (t : Term σ Var) : Finset (Term σ Var) := by
  classical
  exact subtermsWith t

@[simp] theorem subterms_var {σ : Signature.{uSym}} {Var : Type uVar}
    (v : Var) : (Term.var v : Term σ Var).subterms = {Term.var v} := by
  classical
  simp [subterms, subtermsWith]

@[simp] theorem subterms_app {σ : Signature.{uSym}} {Var : Type uVar}
    (s : σ.Symbol) (args : Fin (σ.arity s) → Term σ Var) :
    (Term.app s args).subterms =
      insert (Term.app s args)
        (Finset.univ.biUnion (fun p => (args p).subterms)) := by
  classical
  simp [subterms, subtermsWith]

theorem self_mem_subterms {σ : Signature.{uSym}} {Var : Type uVar}
    (t : Term σ Var) : t ∈ t.subterms := by
  classical
  cases t with
  | var v => rw [subterms_var]; exact Finset.mem_singleton_self _
  | app s args => rw [subterms_app]; exact Finset.mem_insert_self _ _

theorem child_mem_subterms {σ : Signature.{uSym}} {Var : Type uVar}
    (s : σ.Symbol) (args : Fin (σ.arity s) → Term σ Var)
    (p : Fin (σ.arity s)) : args p ∈ (Term.app s args).subterms := by
  classical
  rw [subterms_app]
  apply Finset.mem_insert_of_mem
  exact Finset.mem_biUnion.mpr
    ⟨p, Finset.mem_univ p, self_mem_subterms (args p)⟩

/-- Subterm sets are transitively closed. -/
theorem subterms_subset_of_mem {σ : Signature.{uSym}} {Var : Type uVar}
    {t u : Term σ Var} (h : t ∈ u.subterms) : t.subterms ⊆ u.subterms := by
  classical
  induction u with
  | var v =>
      simp only [subterms_var, Finset.mem_singleton] at h
      subst t
      exact fun _ hx => hx
  | app s args ih =>
      simp only [subterms_app, Finset.mem_insert, Finset.mem_biUnion,
        Finset.mem_univ, true_and] at h
      rcases h with rfl | ⟨p, hp⟩
      · exact fun _ hx => hx
      · intro x hx
        have hxchild : x ∈ (args p).subterms := ih p hp hx
        simp only [subterms_app, Finset.mem_insert, Finset.mem_biUnion,
          Finset.mem_univ, true_and]
        exact Or.inr ⟨p, hxchild⟩

/-- Predicate selecting non-variable (application) terms. -/
def IsApplication {σ : Signature.{uSym}} {Var : Type uVar} :
    Term σ Var → Prop
  | .var _ => False
  | .app _ _ => True

end Term

namespace TermTheory

/-- The finite union of all subterms occurring in a finite term theory. -/
noncomputable def subterms {σ : Signature.{uSym}} {Var : Type uVar}
    {m : Nat} (Γ : TermTheory σ Var m) : Finset (Term σ Var) := by
  classical
  exact Finset.univ.biUnion (fun i =>
    (Γ i).lhs.subterms ∪ (Γ i).rhs.subterms)

theorem lhs_mem_subterms {σ : Signature.{uSym}} {Var : Type uVar}
    {m : Nat} (Γ : TermTheory σ Var m) (i : Fin m) :
    (Γ i).lhs ∈ Γ.subterms := by
  classical
  unfold subterms
  exact Finset.mem_biUnion.mpr
    ⟨i, Finset.mem_univ i,
      Finset.mem_union_left _ (Term.self_mem_subterms (Γ i).lhs)⟩

theorem rhs_mem_subterms {σ : Signature.{uSym}} {Var : Type uVar}
    {m : Nat} (Γ : TermTheory σ Var m) (i : Fin m) :
    (Γ i).rhs ∈ Γ.subterms := by
  classical
  unfold subterms
  exact Finset.mem_biUnion.mpr
    ⟨i, Finset.mem_univ i,
      Finset.mem_union_right _ (Term.self_mem_subterms (Γ i).rhs)⟩

/-- The finite theory subterm set is closed under taking subterms. -/
theorem subterms_closed {σ : Signature.{uSym}} {Var : Type uVar}
    {m : Nat} (Γ : TermTheory σ Var m) {t u : Term σ Var}
    (ht : t ∈ Γ.subterms) (hu : u ∈ t.subterms) : u ∈ Γ.subterms := by
  classical
  simp only [subterms, Finset.mem_biUnion, Finset.mem_univ, true_and] at ht ⊢
  obtain ⟨i, hi⟩ := ht
  rcases Finset.mem_union.mp hi with hil | hir
  · exact ⟨i, Finset.mem_union_left _
      (Term.subterms_subset_of_mem hil hu)⟩
  · exact ⟨i, Finset.mem_union_right _
      (Term.subterms_subset_of_mem hir hu)⟩

end TermTheory

namespace FiniteFlattening

/-- A non-variable subterm of the input theory, presented by its symbol,
ordered children, and finite-subterm membership proof. -/
structure AppSubterm {σ : Signature.{uSym}} {Original : Type uVar} {m : Nat}
    (Γ : TermTheory σ Original m) where
  symbol : σ.Symbol
  args : Fin (σ.arity symbol) → Term σ Original
  mem : Term.app symbol args ∈ Γ.subterms

namespace AppSubterm

def term {σ : Signature.{uSym}} {Original : Type uVar} {m : Nat}
    {Γ : TermTheory σ Original m} (u : AppSubterm Γ) : Term σ Original :=
  Term.app u.symbol u.args

end AppSubterm

/-- Original variables plus one auxiliary variable for every distinct
non-variable subterm. -/
abbrev Var {σ : Signature.{uSym}} {Original : Type uVar} {m : Nat}
    (Γ : TermTheory σ Original m) := Original ⊕ AppSubterm Γ

noncomputable instance appSubtermFintype {σ : Signature.{uSym}}
    {Original : Type uVar} {m : Nat} (Γ : TermTheory σ Original m) :
    Fintype (AppSubterm Γ) := by
  classical
  let f : AppSubterm Γ → {t : Term σ Original // t ∈ Γ.subterms} :=
    fun t => ⟨t.term, t.mem⟩
  letI : Finite (AppSubterm Γ) :=
    Finite.of_injective f (fun x y h => by
      have hterm : x.term = y.term := congrArg
        (fun z : {t : Term σ Original // t ∈ Γ.subterms} => z.1) h
      cases x with
      | mk sx ax hx =>
          cases y with
          | mk sy ay hy =>
              simp only [AppSubterm.term] at hterm
              cases hterm
              rfl)
  exact Fintype.ofFinite _

noncomputable instance varFintype {σ : Signature.{uSym}}
    {Original : Type uVar} {m : Nat} [Fintype Original]
    (Γ : TermTheory σ Original m) : Fintype (Var Γ) :=
  Fintype.ofFinite _

/-- The flat variable representing a theory subterm known to belong to the
finite subterm set. -/
def varOfTerm {σ : Signature.{uSym}} {Original : Type uVar} {m : Nat}
    (Γ : TermTheory σ Original m) (t : Term σ Original)
    (ht : t ∈ Γ.subterms) : Var Γ :=
  match t with
  | .var v => .inl v
  | .app s args => .inr ⟨s, args, ht⟩

/-- The defining normal-form equation associated with one non-variable
subterm. -/
def definingEquation {σ : Signature.{uSym}} {Original : Type uVar}
    {m : Nat} (Γ : TermTheory σ Original m) (u : AppSubterm Γ) :
    Equation σ (Var Γ) :=
  { symbol := u.symbol
    args := fun p =>
      varOfTerm Γ (u.args p)
        (TermTheory.subterms_closed Γ u.mem
          (Term.child_mem_subterms u.symbol u.args p))
    output := .inr u }

/-- Satisfaction of every finite defining equation. -/
def DefiningEquationsHold {σ : Signature.{uSym}} {Original : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermTheory σ Original m)
    (I : Interpretation σ A) (b : Assignment (Var Γ) A) : Prop :=
  ∀ u : AppSubterm Γ, (definingEquation Γ u).Holds I b

/-- Restrict a finite flat assignment to the original variables. -/
def restrict {σ : Signature.{uSym}} {Original : Type uVar}
    {A : Type uAlpha} {m : Nat} {Γ : TermTheory σ Original m}
    (b : Assignment (Var Γ) A) : Assignment Original A :=
  fun v => b (.inl v)

/-- Extend an original assignment by evaluating every finite auxiliary
subterm. -/
def extend {σ : Signature.{uSym}} {Original : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermTheory σ Original m)
    (I : Interpretation σ A) (a : Assignment Original A) :
    Assignment (Var Γ) A
  | .inl v => a v
  | .inr u => u.term.eval I a

/-- The extension value at the flat variable of a subterm is its evaluation. -/
theorem extend_varOfTerm {σ : Signature.{uSym}} {Original : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermTheory σ Original m)
    (I : Interpretation σ A) (a : Assignment Original A)
    (t : Term σ Original) (ht : t ∈ Γ.subterms) :
    extend Γ I a (varOfTerm Γ t ht) = t.eval I a := by
  cases t <;> rfl

/-- Canonical evaluation extension satisfies all finite defining equations. -/
theorem extend_definingEquationsHold {σ : Signature.{uSym}}
    {Original : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermTheory σ Original m) (I : Interpretation σ A)
    (a : Assignment Original A) :
    DefiningEquationsHold Γ I (extend Γ I a) := by
  intro u
  change I u.symbol (fun p => extend Γ I a (varOfTerm Γ (u.args p) _)) =
    extend Γ I a (.inr u)
  change I u.symbol (fun p => extend Γ I a (varOfTerm Γ (u.args p) _)) =
    (Term.app u.symbol u.args).eval I a
  congr 1
  funext p
  exact extend_varOfTerm Γ I a (u.args p) _

/-- Finite uniqueness of auxiliary values, proved by structural induction. -/
theorem value_varOfTerm_eq_eval {σ : Signature.{uSym}}
    {Original : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermTheory σ Original m) (I : Interpretation σ A)
    (b : Assignment (Var Γ) A) (h : DefiningEquationsHold Γ I b)
    (t : Term σ Original) (ht : t ∈ Γ.subterms) :
    b (varOfTerm Γ t ht) = t.eval I (restrict b) := by
  induction t with
  | var v => rfl
  | app s args ih =>
      let u : AppSubterm Γ := ⟨s, args, ht⟩
      have hdef := h u
      change I s (fun p => b (varOfTerm Γ (args p) _)) = b (.inr u) at hdef
      calc
        b (varOfTerm Γ (Term.app s args) ht) = b (.inr u) := rfl
        _ = I s (fun p => b (varOfTerm Γ (args p) _)) := hdef.symm
        _ = I s (fun p => (args p).eval I (restrict b)) := by
          congr 1
          funext p
          exact ih p _
        _ = (Term.app s args).eval I (restrict b) := rfl

/-- The complete finite flat system: defining equations plus one variable
equality for each original term equation. -/
def Holds {σ : Signature.{uSym}} {Original : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermTheory σ Original m)
    (I : Interpretation σ A) (b : Assignment (Var Γ) A) : Prop :=
  DefiningEquationsHold Γ I b ∧
    ∀ i, b (varOfTerm Γ (Γ i).lhs (TermTheory.lhs_mem_subterms Γ i)) =
      b (varOfTerm Γ (Γ i).rhs (TermTheory.rhs_mem_subterms Γ i))

/-- Exact finite flattening equivalence, before quotienting its explicit
variable equalities. -/
def solutionsEquiv {σ : Signature.{uSym}} {Original : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermTheory σ Original m)
    (I : Interpretation σ A) :
    TypeEquiv (TermTheory.Solutions Γ I)
      {b : Assignment (Var Γ) A // Holds Γ I b} where
  toFun a :=
    ⟨extend Γ I a.1,
      ⟨extend_definingEquationsHold Γ I a.1, fun i => by
        simpa only [extend_varOfTerm] using a.2 i⟩⟩
  invFun b :=
    ⟨restrict b.1, fun i => by
      simpa only [value_varOfTerm_eq_eval Γ I b.1 b.2.1] using b.2.2 i⟩
  left_inv a := by
    apply Subtype.ext
    rfl
  right_inv b := by
    apply Subtype.ext
    funext v
    cases v with
    | inl original => rfl
    | inr u =>
        change extend Γ I (restrict b.1) (.inr u) = b.1 (.inr u)
        exact (value_varOfTerm_eq_eval Γ I b.1 b.2.1 u.term u.mem).symm

/-- Number of distinct non-variable subterms, hence number of finite defining
equations. -/
noncomputable def equationCount {σ : Signature.{uSym}} {Original : Type uVar}
    {m : Nat} (Γ : TermTheory σ Original m) : Nat :=
  Fintype.card (AppSubterm Γ)

/-- Enumerate the finite non-variable subterms by `Fin`. -/
noncomputable def appSubtermAt {σ : Signature.{uSym}}
    {Original : Type uVar} {m : Nat} (Γ : TermTheory σ Original m) :
    Fin (equationCount Γ) → AppSubterm Γ :=
  (Fintype.equivFin (AppSubterm Γ)).symm

/-- The finite normal-form defining system before quotienting variable
equalities. -/
noncomputable def definingSystem {σ : Signature.{uSym}}
    {Original : Type uVar} {m : Nat} (Γ : TermTheory σ Original m) :
    TermSystem σ (Var Γ) (equationCount Γ) :=
  fun i => definingEquation Γ (appSubtermAt Γ i)

/-- The explicit flat variable equalities induced by the original term
equations. -/
def originalEqualities {σ : Signature.{uSym}} {Original : Type uVar}
    {m : Nat} (Γ : TermTheory σ Original m) :
    TermSystem.VariableEqualities (Var Γ) m :=
  fun i =>
    (varOfTerm Γ (Γ i).lhs (TermTheory.lhs_mem_subterms Γ i),
      varOfTerm Γ (Γ i).rhs (TermTheory.rhs_mem_subterms Γ i))

theorem definingSystem_holds_iff {σ : Signature.{uSym}}
    {Original : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermTheory σ Original m) (I : Interpretation σ A)
    (b : Assignment (Var Γ) A) :
    TermSystem.Holds (definingSystem Γ) I b ↔
      DefiningEquationsHold Γ I b := by
  constructor
  · intro h u
    let i := Fintype.equivFin (AppSubterm Γ) u
    have hi := h i
    simpa only [definingSystem, appSubtermAt, i,
      Equiv.symm_apply_apply] using hi
  · intro h i
    exact h (appSubtermAt Γ i)

theorem holds_iff_definingSystem_and_equalities {σ : Signature.{uSym}}
    {Original : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermTheory σ Original m) (I : Interpretation σ A)
    (b : Assignment (Var Γ) A) :
    Holds Γ I b ↔
      TermSystem.Holds (definingSystem Γ) I b ∧
        (originalEqualities Γ).Holds b := by
  constructor
  · intro h
    exact ⟨(definingSystem_holds_iff Γ I b).2 h.1, h.2⟩
  · intro h
    exact ⟨(definingSystem_holds_iff Γ I b).1 h.1, h.2⟩

/-- Repackage finite flat solutions as solutions of the enumerated defining
system together with its explicit variable equalities. -/
def flatSolutionsEquivExplicitEqualities {σ : Signature.{uSym}}
    {Original : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermTheory σ Original m) (I : Interpretation σ A) :
    TypeEquiv {b : Assignment (Var Γ) A // Holds Γ I b}
      {b : Assignment (Var Γ) A //
        TermSystem.Holds (definingSystem Γ) I b ∧
          (originalEqualities Γ).Holds b} where
  toFun b := ⟨b.1, (holds_iff_definingSystem_and_equalities Γ I b.1).1 b.2⟩
  invFun b := ⟨b.1, (holds_iff_definingSystem_and_equalities Γ I b.1).2 b.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The finite flat normal-form system after quotienting the explicit
equalities generated by the original equations. This is Step 3 of
Proposition 3.2, before collision closure. -/
noncomputable def normalFormSystem {σ : Signature.{uSym}}
    {Original : Type uVar} {m : Nat} (Γ : TermTheory σ Original m) :=
  TermSystem.variableQuotient (definingSystem Γ)
    (TermSystem.equalitySetoid (originalEqualities Γ))

/-- Exact finite normalisation equivalence through flattening and variable
quotienting. The remaining collision-closure step is separated so its
termination and no-collision postcondition cannot be hidden here. -/
noncomputable def normalFormSolutionsEquiv {σ : Signature.{uSym}}
    {Original : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermTheory σ Original m) (I : Interpretation σ A) :
    TypeEquiv (TermTheory.Solutions Γ I)
      (TermSystem.Solutions (normalFormSystem Γ) I) :=
  (solutionsEquiv Γ I).trans
    ((flatSolutionsEquivExplicitEqualities Γ I).trans
      (TermSystem.explicitEqualitiesSolutionsEquiv
        (definingSystem Γ) (originalEqualities Γ) I))

end FiniteFlattening

end TermCoding
