import TermCoding.Terms

namespace TermCoding

universe uSym uVar uAlpha

/-- The semantic all-subterms flattening uses an original-variable vertex and
one auxiliary vertex for every non-variable term. The paper's finite
normalisation is obtained by restricting this construction to the finite
subterm closure of the input theory. -/
inductive FlatVar (σ : Signature.{uSym}) (Var : Type uVar) where
  | original (v : Var)
  | auxiliary (symbol : σ.Symbol)
      (args : Fin (σ.arity symbol) → Term σ Var)

namespace FlatVar

/-- The flat variable representing a term: an original vertex for a variable,
and the corresponding auxiliary vertex for an application. -/
def ofTerm {σ : Signature.{uSym}} {Var : Type uVar} :
    Term σ Var → FlatVar σ Var
  | .var v => .original v
  | .app s args => .auxiliary s args

end FlatVar

namespace SemanticFlattening

/-- Restrict a flat assignment to the original variables. -/
def restrict {σ : Signature.{uSym}} {Var : Type uVar} {A : Type uAlpha}
    (b : Assignment (FlatVar σ Var) A) : Assignment Var A :=
  fun v => b (.original v)

/-- Extend an original assignment by evaluating every non-variable term. -/
def extend {σ : Signature.{uSym}} {Var : Type uVar} {A : Type uAlpha}
    (I : Interpretation σ A) (a : Assignment Var A) :
    Assignment (FlatVar σ Var) A
  | .original v => a v
  | .auxiliary s args => (Term.app s args).eval I a

/-- Every defining flat equation holds. This predicate is the semantic
all-subterms version of the paper's finite family of defining equations. -/
def DefiningEquationsHold {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} (I : Interpretation σ A)
    (b : Assignment (FlatVar σ Var) A) : Prop :=
  ∀ (s : σ.Symbol) (args : Fin (σ.arity s) → Term σ Var),
    I s (fun p => b (FlatVar.ofTerm (args p))) =
      b (.auxiliary s args)

/-- The extended value at the flat vertex of a term is its evaluation. -/
theorem extend_ofTerm {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} (I : Interpretation σ A) (a : Assignment Var A)
    (t : Term σ Var) :
    extend I a (FlatVar.ofTerm t) = t.eval I a := by
  cases t <;> simp only [FlatVar.ofTerm, extend, Term.eval]

/-- The canonical evaluation extension satisfies all defining equations. -/
theorem extend_definingEquationsHold {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} (I : Interpretation σ A)
    (a : Assignment Var A) : DefiningEquationsHold I (extend I a) := by
  intro s args
  simp only [extend]
  congr 1
  funext p
  exact extend_ofTerm I a (args p)

/-- Uniqueness of auxiliary values: any assignment satisfying all defining
equations assigns to every term vertex its evaluation under the restricted
original assignment. -/
theorem value_ofTerm_eq_eval {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} (I : Interpretation σ A)
    (b : Assignment (FlatVar σ Var) A) (h : DefiningEquationsHold I b)
    (t : Term σ Var) :
    b (FlatVar.ofTerm t) = t.eval I (restrict b) := by
  induction t with
  | var v => rfl
  | app s args ih =>
      calc
        b (.auxiliary s args) =
            I s (fun p => b (FlatVar.ofTerm (args p))) := (h s args).symm
        _ = I s (fun p => (args p).eval I (restrict b)) := by
          congr 1
          funext p
          exact ih p
        _ = (Term.app s args).eval I (restrict b) := rfl

/-- The all-subterms flat system consists of its defining equations together
with one equality between the flat vertices of each original equation. -/
def Holds {σ : Signature.{uSym}} {Var : Type uVar} {A : Type uAlpha}
    {m : Nat} (Γ : TermTheory σ Var m) (I : Interpretation σ A)
    (b : Assignment (FlatVar σ Var) A) : Prop :=
  DefiningEquationsHold I b ∧
    ∀ i, b (FlatVar.ofTerm (Γ i).lhs) = b (FlatVar.ofTerm (Γ i).rhs)

/-- Exact semantic flattening equivalence. This checks the extension,
restriction, and uniqueness core of Proposition 3.2. Finiteness of the chosen
subterm family and the subsequent quotient/collision closure are separate
obligations. -/
def allTermsFlatSolutionsEquiv {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermTheory σ Var m)
    (I : Interpretation σ A) :
    TypeEquiv (TermTheory.Solutions Γ I)
      {b : Assignment (FlatVar σ Var) A // Holds Γ I b} where
  toFun a :=
    ⟨extend I a.1,
      ⟨extend_definingEquationsHold I a.1, fun i => by
        simpa only [extend_ofTerm] using a.2 i⟩⟩
  invFun b :=
    ⟨restrict b.1, fun i => by
      simpa only [value_ofTerm_eq_eval I b.1 b.2.1] using b.2.2 i⟩
  left_inv a := by
    apply Subtype.ext
    rfl
  right_inv b := by
    apply Subtype.ext
    funext v
    cases v with
    | original v => rfl
    | auxiliary s args =>
        change extend I (restrict b.1) (.auxiliary s args) =
          b.1 (.auxiliary s args)
        simpa only [extend] using
          (value_ofTerm_eq_eval I b.1 b.2.1 (Term.app s args)).symm

end SemanticFlattening

end TermCoding
