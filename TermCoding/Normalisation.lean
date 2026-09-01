import TermCoding.FiniteFlattening
import TermCoding.CollisionClosure

namespace TermCoding

universe uSym uVar uAlpha

namespace Normalisation

/-- Variable type of the complete collision-free normal form. -/
abbrev Variable {σ : Signature.{uSym}} {Original : Type uVar} {m : Nat}
    (Γ : TermTheory σ Original m) :=
  Quotient (TermSystem.collisionSetoid
    (FiniteFlattening.normalFormSystem Γ))

noncomputable instance variableFintype {σ : Signature.{uSym}}
    {Original : Type uVar} {m : Nat} [Fintype Original]
    (Γ : TermTheory σ Original m) : Fintype (Variable Γ) :=
  Fintype.ofFinite _

noncomputable instance variableNonempty {σ : Signature.{uSym}}
    {Original : Type uVar} {m : Nat} [Nonempty Original]
    (Γ : TermTheory σ Original m) : Nonempty (Variable Γ) := by
  let v : Original := Classical.choice inferInstance
  let flat : FiniteFlattening.Var Γ := Sum.inl v
  let qflat : Quotient
      (TermSystem.equalitySetoid (FiniteFlattening.originalEqualities Γ)) :=
    Quotient.mk _ flat
  exact ⟨Quotient.mk
    (TermSystem.collisionSetoid (FiniteFlattening.normalFormSystem Γ)) qflat⟩

/-- Number of variables after flattening and all forced quotients. -/
noncomputable def variableCount {σ : Signature.{uSym}}
    {Original : Type uVar} {m : Nat} [Fintype Original]
    (Γ : TermTheory σ Original m) : Nat :=
  Fintype.card (Variable Γ)

/-- The complete finite normal form from Proposition 3.2: finite subterm
flattening, quotienting the original root equalities, canonical collision
closure, and duplicate removal. -/
noncomputable def system {σ : Signature.{uSym}} {Original : Type uVar}
    {m : Nat} (Γ : TermTheory σ Original m) :=
  TermSystem.collisionFreeSystem (FiniteFlattening.normalFormSystem Γ)

/-- The constructed finite normal form satisfies the exact Term-DAG/
no-collision hypothesis used by the diversification lower bound. -/
theorem system_noCollision {σ : Signature.{uSym}} {Original : Type uVar}
    {m : Nat} (Γ : TermTheory σ Original m) :
    TermSystem.NoCollision (system Γ) :=
  TermSystem.collisionFreeSystem_noCollision
    (FiniteFlattening.normalFormSystem Γ)

/-- Complete exact solution equivalence for Proposition 3.2, for every fixed
interpretation. -/
noncomputable def solutionsEquiv {σ : Signature.{uSym}}
    {Original : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermTheory σ Original m) (I : Interpretation σ A) :
    TypeEquiv (TermTheory.Solutions Γ I)
      (TermSystem.Solutions (system Γ) I) :=
  (FiniteFlattening.normalFormSolutionsEquiv Γ I).trans
    (TermSystem.collisionFreeSolutionsEquiv
      (FiniteFlattening.normalFormSystem Γ) I)

end Normalisation

end TermCoding
