import Mathlib
import TermCoding.BlockEmbedding
import TermCoding.VariableQuotient

namespace TermCoding

universe uSym uVar uAlpha

namespace TermSystem

/-- The least equivalence relation on variables closed under the rule that
equal argument tuples for the same operation force equal outputs. This is a
canonical form of the paper's iterative collision closure. -/
inductive CollisionEqv {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}
    (Γ : TermSystem σ Var m) : Var → Var → Prop
  | refl (x : Var) : CollisionEqv Γ x x
  | symm {x y : Var} : CollisionEqv Γ x y → CollisionEqv Γ y x
  | trans {x y z : Var} :
      CollisionEqv Γ x y → CollisionEqv Γ y z → CollisionEqv Γ x z
  | collision {s : σ.Symbol}
      (args₁ args₂ : Fin (σ.arity s) → Var) (out₁ out₂ : Var)
      (i j : Fin m)
      (hi : Γ i = { symbol := s, args := args₁, output := out₁ })
      (hj : Γ j = { symbol := s, args := args₂, output := out₂ })
      (hargs : ∀ p, CollisionEqv Γ (args₁ p) (args₂ p)) :
      CollisionEqv Γ out₁ out₂

/-- The collision relation as a `Setoid`, ready for quotienting. -/
def collisionSetoid {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}
    (Γ : TermSystem σ Var m) : Setoid Var where
  r := CollisionEqv Γ
  iseqv :=
    { refl := CollisionEqv.refl
      symm := CollisionEqv.symm
      trans := CollisionEqv.trans }

/-- Every solution assignment is constant on collision-closure classes. -/
theorem solution_compatible_collision {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (I : Interpretation σ A)
    (a : Assignment Var A) (ha : Holds Γ I a) :
    Compatible (collisionSetoid Γ) a := by
  intro x y hxy
  change CollisionEqv Γ x y at hxy
  induction hxy with
  | refl x => rfl
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | collision args₁ args₂ out₁ out₂ i j hi hj hargs ih =>
      have hEi := ha i
      have hEj := ha j
      rw [hi] at hEi
      rw [hj] at hEj
      change I _ (fun p => a (args₁ p)) = a out₁ at hEi
      change I _ (fun p => a (args₂ p)) = a out₂ at hEj
      have hinputs : (fun p => a (args₁ p)) = (fun p => a (args₂ p)) := by
        funext p
        exact ih p
      rw [hinputs] at hEi
      exact hEi.symm.trans hEj

/-- Quotienting by canonical collision closure preserves the exact solution
type for each fixed interpretation. -/
def collisionQuotientSolutionsEquiv {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (I : Interpretation σ A) :
    TypeEquiv (Solutions Γ I)
      (Solutions (variableQuotient Γ (collisionSetoid Γ)) I) where
  toFun a :=
    ⟨descendAssignment (collisionSetoid Γ) a.1
        (solution_compatible_collision Γ I a.1 a.2),
      (variableQuotient_holds_iff Γ (collisionSetoid Γ) I _).2 (by
        rw [pullback_descend]
        exact a.2)⟩
  invFun a :=
    ⟨pullbackAssignment (collisionSetoid Γ) a.1,
      (variableQuotient_holds_iff Γ (collisionSetoid Γ) I a.1).1 a.2⟩
  left_inv a := by
    apply Subtype.ext
    exact pullback_descend (collisionSetoid Γ) a.1
      (solution_compatible_collision Γ I a.1 a.2)
  right_inv a := by
    apply Subtype.ext
    exact descend_pullback (collisionSetoid Γ) a.1

/-- A system is left-functional when colliding left-hand sides have equal
outputs. Duplicate identical equations may still be present. -/
def LeftFunctional {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}
    (Γ : TermSystem σ Var m) : Prop :=
  ∀ i j, (Γ i).leftSide = (Γ j).leftSide →
    (Γ i).output = (Γ j).output

/-- The canonical collision quotient is left-functional. -/
theorem collisionQuotient_leftFunctional {σ : Signature.{uSym}}
    {Var : Type uVar} {m : Nat} (Γ : TermSystem σ Var m) :
    LeftFunctional (variableQuotient Γ (collisionSetoid Γ)) := by
  intro i j hleft
  cases hi : Γ i with
  | mk si ai oi =>
      cases hj : Γ j with
      | mk sj aj oj =>
          simp only [variableQuotient, Equation.leftSide] at hleft ⊢
          rw [hi, hj] at hleft ⊢
          change
            (⟨si, fun p => Quotient.mk (collisionSetoid Γ) (ai p)⟩ :
              OperationQuery σ (Quotient (collisionSetoid Γ))) =
            ⟨sj, fun p => Quotient.mk (collisionSetoid Γ) (aj p)⟩ at hleft
          have hs : si = sj := (Sigma.ext_iff.mp hleft).1
          subst sj
          have hargsQ :
              (fun p => Quotient.mk (collisionSetoid Γ) (ai p)) =
                (fun p => Quotient.mk (collisionSetoid Γ) (aj p)) :=
            eq_of_heq (Sigma.ext_iff.mp hleft).2
          have hargs : ∀ p, CollisionEqv Γ (ai p) (aj p) := by
            intro p
            exact Quotient.exact (congrFun hargsQ p)
          change Quotient.mk (collisionSetoid Γ) oi =
            Quotient.mk (collisionSetoid Γ) oj
          exact Quotient.sound
            (CollisionEqv.collision ai aj oi oj i j hi hj hargs)

/-- Two normal-form equations are equal if both their left sides and outputs
are equal. -/
theorem equation_eq_of_leftSide_eq_output_eq {σ : Signature.{uSym}}
    {Var : Type uVar} {e₁ e₂ : Equation σ Var}
    (hl : e₁.leftSide = e₂.leftSide) (ho : e₁.output = e₂.output) :
    e₁ = e₂ := by
  cases e₁ with
  | mk s₁ a₁ o₁ =>
      cases e₂ with
      | mk s₂ a₂ o₂ =>
          change (⟨s₁, a₁⟩ : OperationQuery σ Var) = ⟨s₂, a₂⟩ at hl
          have hs : s₁ = s₂ := (Sigma.ext_iff.mp hl).1
          subst s₂
          have ha : a₁ = a₂ := eq_of_heq (Sigma.ext_iff.mp hl).2
          subst a₂
          simp only at ho
          subst o₂
          rfl

/-- The finite set of distinct equations occurring in an indexed system. -/
noncomputable def equationFinset {σ : Signature.{uSym}} {Var : Type uVar}
    {m : Nat} (Γ : TermSystem σ Var m) : Finset (Equation σ Var) := by
  classical
  exact Finset.univ.image Γ

def DistinctEquation {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}
    (Γ : TermSystem σ Var m) :=
  {e : Equation σ Var // e ∈ equationFinset Γ}

noncomputable instance distinctEquationFintype {σ : Signature.{uSym}}
    {Var : Type uVar} {m : Nat} (Γ : TermSystem σ Var m) :
    Fintype (DistinctEquation Γ) := by
  classical
  exact Fintype.ofFinset (equationFinset Γ) (fun _ => Iff.rfl)

noncomputable def deduplicatedCount {σ : Signature.{uSym}}
    {Var : Type uVar} {m : Nat} (Γ : TermSystem σ Var m) : Nat :=
  Fintype.card (DistinctEquation Γ)

noncomputable def deduplicatedAt {σ : Signature.{uSym}}
    {Var : Type uVar} {m : Nat} (Γ : TermSystem σ Var m) :
    Fin (deduplicatedCount Γ) → DistinctEquation Γ :=
  (Fintype.equivFin (DistinctEquation Γ)).symm

/-- Enumerate each distinct equation exactly once. -/
noncomputable def deduplicate {σ : Signature.{uSym}} {Var : Type uVar}
    {m : Nat} (Γ : TermSystem σ Var m) :
    TermSystem σ Var (deduplicatedCount Γ) :=
  fun i => (deduplicatedAt Γ i).1

/-- Removing duplicate equations preserves the satisfaction predicate. -/
theorem deduplicate_holds_iff {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m)
    (I : Interpretation σ A) (a : Assignment Var A) :
    Holds (deduplicate Γ) I a ↔ Holds Γ I a := by
  classical
  constructor
  · intro h i
    let e : DistinctEquation Γ :=
      ⟨Γ i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
    let j := Fintype.equivFin (DistinctEquation Γ) e
    have hj := h j
    simpa only [deduplicate, deduplicatedAt, j, e,
      Equiv.symm_apply_apply] using hj
  · intro h j
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (deduplicatedAt Γ j).2
    change (deduplicatedAt Γ j).1.Holds I a
    rw [← hi]
    exact h i

def deduplicateSolutionsEquiv {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m)
    (I : Interpretation σ A) :
    TypeEquiv (Solutions Γ I) (Solutions (deduplicate Γ) I) where
  toFun a := ⟨a.1, (deduplicate_holds_iff Γ I a.1).2 a.2⟩
  invFun a := ⟨a.1, (deduplicate_holds_iff Γ I a.1).1 a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Deduplicating a left-functional system yields the exact no-collision
property required by the block-embedding theorem. -/
theorem deduplicate_noCollision_of_leftFunctional
    {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}
    (Γ : TermSystem σ Var m) (hΓ : LeftFunctional Γ) :
    NoCollision (deduplicate Γ) := by
  classical
  intro i j hleft
  obtain ⟨ii, _, hii⟩ := Finset.mem_image.mp (deduplicatedAt Γ i).2
  obtain ⟨jj, _, hjj⟩ := Finset.mem_image.mp (deduplicatedAt Γ j).2
  have hleft' : (Γ ii).leftSide = (Γ jj).leftSide := by
    simpa only [deduplicate, hii, hjj] using hleft
  have hout : (Γ ii).output = (Γ jj).output := hΓ ii jj hleft'
  have heq : (deduplicatedAt Γ i).1 = (deduplicatedAt Γ j).1 := by
    rw [← hii, ← hjj]
    exact equation_eq_of_leftSide_eq_output_eq hleft' hout
  have hsub : deduplicatedAt Γ i = deduplicatedAt Γ j := Subtype.ext heq
  exact (Fintype.equivFin (DistinctEquation Γ)).symm.injective hsub

/-- Canonical collision-free system: quotient by collision closure and then
remove duplicate identical equations. -/
noncomputable def collisionFreeSystem {σ : Signature.{uSym}}
    {Var : Type uVar} {m : Nat} (Γ : TermSystem σ Var m) :=
  deduplicate (variableQuotient Γ (collisionSetoid Γ))

theorem collisionFreeSystem_noCollision {σ : Signature.{uSym}}
    {Var : Type uVar} {m : Nat} (Γ : TermSystem σ Var m) :
    NoCollision (collisionFreeSystem Γ) :=
  deduplicate_noCollision_of_leftFunctional _
    (collisionQuotient_leftFunctional Γ)

/-- Exact solution equivalence for the complete collision-closure step. -/
noncomputable def collisionFreeSolutionsEquiv {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (I : Interpretation σ A) :
    TypeEquiv (Solutions Γ I) (Solutions (collisionFreeSystem Γ) I) :=
  (collisionQuotientSolutionsEquiv Γ I).trans
    (deduplicateSolutionsEquiv
      (variableQuotient Γ (collisionSetoid Γ)) I)

end TermSystem

end TermCoding
