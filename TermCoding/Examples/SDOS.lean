namespace TermCoding.Examples.SDOS

universe u

/-- The first two SDOS identities already force commutativity. No finiteness
assumption is needed. -/
theorem commutative_of_first_two {A : Type u} (f : A → A → A)
    (h₁ : ∀ x y, f (f x y) y = x)
    (h₂ : ∀ x y, f x (f y x) = y) :
    ∀ x z, f x z = f z x := by
  intro x z
  calc
    f x z = f x (f (f z x) x) := congrArg (f x) (h₁ z x).symm
    _ = f z x := h₂ x (f z x)

/-- The four universal SDOS identities force the carrier to be a subsingleton.
This is the formal counterpart of Lemma 8.5 in Paper 1. -/
theorem all_eq_of_sdos {A : Type u} (f : A → A → A)
    (h₁ : ∀ x y, f (f x y) y = x)
    (h₂ : ∀ x y, f x (f y x) = y)
    (h₃ : ∀ x y, f (f x y) (f y x) = x)
    (h₄ : ∀ x y, f (f y x) (f x y) = y) :
    ∀ x y : A, x = y := by
  intro x y
  have hcomm := commutative_of_first_two f h₁ h₂
  have hyx : f y x = f x y := hcomm y x
  calc
    x = f (f x y) (f y x) := (h₃ x y).symm
    _ = f (f x y) (f x y) := congrArg (f (f x y)) hyx
    _ = y := by
      have hxy : f x y = f y x := hcomm x y
      exact (congrArg (fun t => f t (f x y)) hxy).trans (h₄ x y)

/-- Hence two distinct elements rule out a universal SDOS interpretation. -/
theorem no_sdos_of_distinct {A : Type u} (f : A → A → A)
    (h₁ : ∀ x y, f (f x y) y = x)
    (h₂ : ∀ x y, f x (f y x) = y)
    (h₃ : ∀ x y, f (f x y) (f y x) = x)
    (h₄ : ∀ x y, f (f y x) (f x y) = y)
    {x y : A} (hne : x ≠ y) : False :=
  hne (all_eq_of_sdos f h₁ h₂ h₃ h₄ x y)

end TermCoding.Examples.SDOS
