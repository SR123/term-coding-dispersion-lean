import Mathlib.Data.ZMod.Basic
import TermCoding.Cardinality

namespace TermCoding

universe u

namespace Examples.NetworkRedundancy

/-- The three equations of the two-source redundancy example at a triple
`(x,y,z)`. -/
structure Holds {A : Type u} (f h₁ h₂ : A → A → A)
    (t : A × (A × A)) : Prop where
  encode : t.2.2 = f t.1 t.2.1
  recoverSecond : h₁ t.1 t.2.2 = t.2.1
  recoverFirst : h₂ t.2.1 t.2.2 = t.1

def Solutions {A : Type u} (f h₁ h₂ : A → A → A) :=
  {t : A × (A × A) // Holds f h₁ h₂ t}

/-- Irrespective of the decoder choices, a satisfying triple is determined
by its two sources because the encoder determines `z`. -/
def solutionsEmbeddingSources {A : Type u} (f h₁ h₂ : A → A → A) :
    Solutions f h₁ h₂ ↪ A × A where
  toFun t := (t.1.1, t.1.2.1)
  inj' := by
    intro s t hst
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun p : A × A => p.1) hst
    · apply Prod.ext
      · exact congrArg (fun p : A × A => p.2) hst
      · have hx : s.1.1 = t.1.1 :=
          congrArg (fun p : A × A => p.1) hst
        have hy : s.1.2.1 = t.1.2.1 :=
          congrArg (fun p : A × A => p.2) hst
        calc
          s.1.2.2 = f s.1.1 s.1.2.1 := s.2.encode
          _ = f t.1.1 t.1.2.1 := congrArg₂ f hx hy
          _ = t.1.2.2 := t.2.encode.symm

/-- Hence every interpretation has at most `|A|²` valid triples. -/
theorem solutionCard_le_sources {A : Type u} [Finite A]
    (f h₁ h₂ : A → A → A) :
    Nat.card (Solutions f h₁ h₂) ≤ Nat.card A ^ 2 := by
  letI : Finite (Solutions f h₁ h₂) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  calc
    Nat.card (Solutions f h₁ h₂) ≤ Nat.card (A × A) :=
      Nat.card_le_card_of_injective (solutionsEmbeddingSources f h₁ h₂)
        (solutionsEmbeddingSources f h₁ h₂).injective
    _ = Nat.card A ^ 2 := by simp [Nat.card_prod, pow_two]

/-- Additive encoding and subtraction decoding on a finite abelian group. -/
def additiveEncoder {A : Type u} [AddCommGroup A] (x y : A) : A := x + y

def additiveRecoverSecond {A : Type u} [AddCommGroup A] (x z : A) : A :=
  z - x

def additiveRecoverFirst {A : Type u} [AddCommGroup A] (y z : A) : A :=
  z - y

/-- Every source pair extends to a valid additive redundancy triple. -/
def additiveTriple {A : Type u} [AddCommGroup A] (p : A × A) :
    Solutions (additiveEncoder (A := A))
      (additiveRecoverSecond (A := A))
      (additiveRecoverFirst (A := A)) := by
  refine ⟨(p.1, (p.2, p.1 + p.2)), ?_⟩
  exact
    { encode := rfl
      recoverSecond := by simp [additiveRecoverSecond]
      recoverFirst := by simp [additiveRecoverFirst] }

/-- The additive construction has exactly one valid triple for every source
pair. -/
def sourcesEquivAdditiveSolutions {A : Type u} [AddCommGroup A] :
    TypeEquiv (A × A)
      (Solutions (additiveEncoder (A := A))
        (additiveRecoverSecond (A := A))
        (additiveRecoverFirst (A := A))) where
  toFun := additiveTriple
  invFun t := (t.1.1, t.1.2.1)
  left_inv p := rfl
  right_inv t := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · exact t.2.encode.symm

/-- Formal counterpart of the manuscript's exact `n²` statement: the
universal upper bound is attained by every finite abelian group alphabet. -/
theorem additiveSolutionCard_eq_sq {A : Type u} [Finite A] [AddCommGroup A] :
    Nat.card
      (Solutions (additiveEncoder (A := A))
        (additiveRecoverSecond (A := A))
        (additiveRecoverFirst (A := A))) = Nat.card A ^ 2 := by
  have hcard := Nat.card_congr (sourcesEquivAdditiveSolutions (A := A)).toEquiv
  simpa [Nat.card_prod, pow_two] using hcard.symm

/-- The manuscript's concrete statement for every positive alphabet size:
use the cyclic group `ZMod n`. -/
theorem zmodSolutionCard_eq_sq (n : Nat) [NeZero n] :
    Nat.card
      (Solutions (additiveEncoder (A := ZMod n))
        (additiveRecoverSecond (A := ZMod n))
        (additiveRecoverFirst (A := ZMod n))) = n ^ 2 := by
  simpa [Nat.card_zmod] using
    (additiveSolutionCard_eq_sq (A := ZMod n))

end Examples.NetworkRedundancy

end TermCoding
