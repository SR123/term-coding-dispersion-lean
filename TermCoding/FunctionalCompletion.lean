import TermCoding.OrdinaryGame

namespace TermCoding

universe uSym uVar uAlpha

namespace TermSystem

/-- Variables in a fully split functional completion.  Every original
equation occurrence receives its own output copy. -/
abbrev CompletionVar (Var : Type uVar) (m : Nat) := Sum Var (Fin m)

/-- The functional core of the completion: the arguments remain original
variables, while equation `i` writes to its own fresh copy variable. -/
def splitCore {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}
    (Γ : TermSystem σ Var m) :
    TermSystem σ (CompletionVar Var m) m :=
  fun i => {
    symbol := (Γ i).symbol
    args := fun p => Sum.inl ((Γ i).args p)
    output := Sum.inr i
  }

/-- The explicit equality constraints identifying every output copy with
the original output variable of its parent equation. -/
def CompletionConsistent {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m)
    (a : Assignment (CompletionVar Var m) A) : Prop :=
  ∀ i, a (Sum.inr i) = a (Sum.inl (Γ i).output)

/-- Satisfaction of the split functional core together with all explicit
copy equalities. -/
def CompletionHolds {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m)
    (I : Interpretation σ A) (a : Assignment (CompletionVar Var m) A) : Prop :=
  (splitCore Γ).Holds I a ∧ CompletionConsistent Γ a

/-- Satisfying assignments of the fully split completion. -/
def CompletionSolutions {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m)
    (I : Interpretation σ A) :=
  {a : Assignment (CompletionVar Var m) A // CompletionHolds Γ I a}

/-- Extend an original assignment by assigning each fresh output copy the
value of its parent output variable. -/
def extendCompletion {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m)
    (a : Assignment Var A) : Assignment (CompletionVar Var m) A :=
  Sum.elim a (fun i => a (Γ i).output)

/-- Forget the fresh output-copy coordinates. -/
def restrictCompletion {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (a : Assignment (CompletionVar Var m) A) : Assignment Var A :=
  fun v => a (Sum.inl v)

/-- The split normal-form core is functional: no two distinct equation
occurrences write to the same output variable. -/
theorem splitCore_outputFunctional {σ : Signature.{uSym}}
    {Var : Type uVar} {m : Nat} (Γ : TermSystem σ Var m) :
    OutputFunctional (splitCore Γ) := by
  intro i j hij
  exact Sum.inr.inj hij

/-- On the canonical extension, the split equations are definitionally the
original equations. -/
theorem splitCore_holds_extend_iff {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (I : Interpretation σ A)
    (a : Assignment Var A) :
    (splitCore Γ).Holds I (extendCompletion Γ a) ↔ Γ.Holds I a := by
  rfl

/-- Every canonical extension satisfies the explicit copy equalities. -/
theorem extendCompletion_consistent {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (a : Assignment Var A) :
    CompletionConsistent Γ (extendCompletion Γ a) := by
  intro i
  rfl

/-- A completed assignment satisfies the split functional core precisely
when its restriction satisfies the original equations, provided the explicit
copy equalities hold. -/
theorem splitCore_holds_iff_restrict_of_consistent
    {σ : Signature.{uSym}} {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (I : Interpretation σ A)
    (a : Assignment (CompletionVar Var m) A)
    (hcopy : CompletionConsistent Γ a) :
    (splitCore Γ).Holds I a ↔ Γ.Holds I (restrictCompletion a) := by
  constructor
  · intro h i
    have hi := h i
    change
      I (Γ i).symbol (fun p => a (Sum.inl ((Γ i).args p))) =
        a (Sum.inr i) at hi
    change
      I (Γ i).symbol
          (fun p => restrictCompletion a ((Γ i).args p)) =
        restrictCompletion a (Γ i).output
    exact hi.trans (hcopy i)
  · intro h i
    have hi := h i
    change
      I (Γ i).symbol
          (fun p => restrictCompletion a ((Γ i).args p)) =
        restrictCompletion a (Γ i).output at hi
    change
      I (Γ i).symbol (fun p => a (Sum.inl ((Γ i).args p))) =
        a (Sum.inr i)
    exact hi.trans (hcopy i).symm

/-- Exact fixed-interpretation solution equivalence for functional
completion.  This is the formal extension/forgetting bijection in the paper's
functional-completion lemma. -/
def completionSolutionsEquiv {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (I : Interpretation σ A) :
    TypeEquiv (Solutions Γ I) (CompletionSolutions Γ I) where
  toFun a :=
    ⟨extendCompletion Γ a.1,
      ⟨(splitCore_holds_extend_iff Γ I a.1).2 a.2,
        extendCompletion_consistent Γ a.1⟩⟩
  invFun b :=
    ⟨restrictCompletion b.1,
      (splitCore_holds_iff_restrict_of_consistent Γ I b.1 b.2.2).1 b.2.1⟩
  left_inv a := by
    apply Subtype.ext
    rfl
  right_inv b := by
    apply Subtype.ext
    funext v
    cases v with
    | inl v => rfl
    | inr i => exact (b.2.2 i).symm

/-- Functional completion preserves the exact number of solutions for every
fixed interpretation. -/
theorem completionSolutionCard_eq {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (I : Interpretation σ A) :
    Nat.card (CompletionSolutions Γ I) = Nat.card (Solutions Γ I) := by
  exact Nat.card_congr (completionSolutionsEquiv Γ I).toEquiv.symm

/-- Number of completed solutions for one interpretation. -/
noncomputable def completionSolutionCount {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (I : Interpretation σ A) : Nat :=
  Nat.card (CompletionSolutions Γ I)

/-- Maximum completed solution count over interpretations of the unchanged
operation signature. -/
noncomputable def completionMaxSolutionCount {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    [Fintype σ.Symbol] [Fintype Var] [Fintype A]
    (Γ : TermSystem σ Var m) : Nat :=
  (Finset.univ : Finset (Interpretation σ A)).sup
    (completionSolutionCount Γ)

/-- Functional completion preserves the finite optimum on every alphabet. -/
theorem completionMaxSolutionCount_eq {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    [Fintype σ.Symbol] [Fintype Var] [Fintype A]
    (Γ : TermSystem σ Var m) :
    completionMaxSolutionCount (A := A) Γ =
      maxSolutionCount (A := A) Γ := by
  classical
  unfold completionMaxSolutionCount maxSolutionCount
  congr 1
  funext I
  exact completionSolutionCard_eq Γ I

end TermSystem

end TermCoding
