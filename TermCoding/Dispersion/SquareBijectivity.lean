import TermCoding.Dispersion.Basic

/-!
# Square perfect dispersion and square bijectivity (V6, Section 6.1)

* `perfectDisp_iff_bij` -- `lem:square-perfect-equals-bij`: on a square
  instance, `∃ n ≥ 2, Disp_n(t) = n^k` ⇔ some interpretation on a finite set
  of size ≥ 2 is surjective ⇔ some such interpretation is bijective.
* `identity_reduction` -- `cor:bij-reduces-perfect`: the identity map is a
  (size-preserving) many-one reduction `BIJ ≤_m Perfect-Disp` on square
  instances.
* `bijective_of_inverseEquations`, `exists_inverseExtension_of_bijective`,
  `exists_inverseExtension_iff` --
  `rem:inverse-extension`: after adjoining `k` genuinely fresh `k`-ary
  symbols `s_1, …, s_k`, the two equation families
  `s_i(t_1(x),…,t_k(x)) = x_i` and `t_i(s_1(y),…,s_k(y)) = y_i` hold
  identically iff the original map is bijective; the fresh symbols are
  quantified freely and the original interpretation is unchanged.
-/

namespace TermCoding

namespace Dispersion

universe uSym uAlpha

section Square

variable {σ : Signature.{uSym}} [Fintype σ.Symbol] {k : Nat}

/-- `lem:square-perfect-equals-bij`, (i) ⇔ (iii): square perfect dispersion
is square bijectivity. -/
theorem perfectDisp_iff_bij (t : Instance σ k k) : PerfectDisp t ↔ BIJ t := by
  rw [perfectDisp_iff_surjectiveWitness]
  constructor
  · rintro ⟨A, hA, hcard, I, hI⟩
    exact ⟨A, hA, hcard, I, (surjective_iff_bijective_square t I).1 hI⟩
  · rintro ⟨A, hA, hcard, I, hI⟩
    exact ⟨A, hA, hcard, I, hI.2⟩

/-- `lem:square-perfect-equals-bij`, (ii) ⇔ (iii) at the level of witnesses. -/
theorem surjectiveWitness_iff_bij (t : Instance σ k k) :
    SurjectiveWitness t ↔ BIJ t := by
  rw [← perfectDisp_iff_surjectiveWitness, perfectDisp_iff_bij]

/-- The manuscript's three-way equivalence in one statement. -/
theorem square_tfae (t : Instance σ k k) :
    [(∃ n, 2 ≤ n ∧ dispN t n = n ^ k), SurjectiveWitness t, BIJ t].TFAE := by
  tfae_have 1 ↔ 2 := perfectDisp_iff_surjectiveWitness t
  tfae_have 2 ↔ 3 := surjectiveWitness_iff_bij t
  tfae_finish

/-- A syntactic many-one reduction between decision problems on dispersion
instances, packaged with an explicit linear output-size bound.  (Lean has no
cost model; the transformers used in this development are structurally
recursive, computable functions, and the size bounds are proved.) -/
structure ManyOneReduction {σ' : Signature.{uSym}} {k' r' : Nat}
    (P : Instance σ k k → Prop) (Q : Instance σ' k' r' → Prop) where
  /-- The syntax transformer. -/
  map : Instance σ k k → Instance σ' k' r'
  /-- Yes/no instances are preserved. -/
  correct : ∀ t, P t ↔ Q (map t)
  /-- Linear output-size bound `‖map t‖ ≤ a·‖t‖ + b`. -/
  a : Nat
  b : Nat
  size_le : ∀ t, (map t).size ≤ a * t.size + b

/-- `cor:bij-reduces-perfect`: the identity transformation reduces `BIJ`
(resp. `BIJ_k`) to the square restriction of `Perfect-Disp`
(resp. `Perfect-Disp_k`), preserving size exactly. -/
def identity_reduction :
    ManyOneReduction (BIJ (σ := σ) (k := k)) (PerfectDisp (σ := σ) (k := k) (r := k)) where
  map := id
  correct := fun t => (perfectDisp_iff_bij t).symm
  a := 1
  b := 0
  size_le := fun t => by simp

end Square

/-! ### The inverse-extension form (`rem:inverse-extension`) -/

section InverseExtension

variable {σ : Signature.{uSym}} {k : Nat} {A : Type uAlpha}

/-- The signature `σ` extended by `k` fresh `k`-ary inverse symbols
`s_1, …, s_k`. -/
def inverseSignature (σ : Signature.{uSym}) (k : Nat) : Signature where
  Symbol := Sum σ.Symbol (Fin k)
  arity
    | Sum.inl f => σ.arity f
    | Sum.inr _ => k

/-- Lift an original term to the extended signature. -/
def liftInv : Term σ (Fin k) → Term (inverseSignature σ k) (Fin k)
  | .var v => .var v
  | .app f args => .app (Sum.inl f) (fun p => liftInv (args p))

/-- The term `s_j(y_1, …, y_k)`. -/
def inverseTerm (j : Fin k) : Term (inverseSignature σ k) (Fin k) :=
  .app (Sum.inr j) (fun l => .var l)

/-- The equation `s_i(t_1(x), …, t_k(x)) = x_i`. -/
def leftInverseEquation (t : Instance σ k k) (i : Fin k) :
    TermEquation (inverseSignature σ k) (Fin k) where
  lhs := .app (Sum.inr i) (fun j => liftInv (t j))
  rhs := .var i

/-- The equation `t_i(s_1(y), …, s_k(y)) = y_i`. -/
def rightInverseEquation (t : Instance σ k k) (i : Fin k) :
    TermEquation (inverseSignature σ k) (Fin k) where
  lhs := (liftInv (t i)).subst (fun j => inverseTerm j)
  rhs := .var i

/-- Restrict an interpretation of the extended signature to the original
symbols. -/
def restrictInv (J : Interpretation (inverseSignature σ k) A) : Interpretation σ A :=
  fun f => J (Sum.inl f)

/-- The tuple-valued map defined by the fresh symbols. -/
def decoder (J : Interpretation (inverseSignature σ k) A) :
    (Fin k → A) → (Fin k → A) :=
  fun y i => J (Sum.inr i) y

/-- Extend an original interpretation by a tuple-valued decoder. -/
def extendInv (I : Interpretation σ A) (S : (Fin k → A) → (Fin k → A)) :
    Interpretation (inverseSignature σ k) A
  | Sum.inl f => I f
  | Sum.inr i => fun y => S y i

@[simp] theorem restrictInv_extendInv (I : Interpretation σ A)
    (S : (Fin k → A) → (Fin k → A)) : restrictInv (extendInv I S) = I := by
  funext f
  rfl

@[simp] theorem decoder_extendInv (I : Interpretation σ A)
    (S : (Fin k → A) → (Fin k → A)) : decoder (extendInv I S) = S := by
  funext y i
  rfl

theorem eval_liftInv (J : Interpretation (inverseSignature σ k) A)
    (x : Fin k → A) :
    ∀ u : Term σ (Fin k), (liftInv u).eval J x = u.eval (restrictInv J) x
  | .var v => rfl
  | .app f args => by
      simp only [liftInv, Term.eval]
      change J (Sum.inl f) _ = J (Sum.inl f) _
      congr 1
      funext p
      exact eval_liftInv J x (args p)

theorem eval_inverseTerm (J : Interpretation (inverseSignature σ k) A)
    (y : Fin k → A) (j : Fin k) : (inverseTerm j).eval J y = decoder J y j := rfl

/-- The left-inverse equations hold identically iff `decoder J` is a left
inverse of `Θ^{J|σ}`. -/
theorem leftInverseEquations_iff (t : Instance σ k k)
    (J : Interpretation (inverseSignature σ k) A) :
    (∀ i x, (leftInverseEquation t i).Holds J x) ↔
      ∀ x, decoder J (termMap t (restrictInv J) x) = x := by
  constructor
  · intro h x
    funext i
    have hi := h i x
    simp only [leftInverseEquation, TermEquation.Holds, Term.eval] at hi
    rw [← hi]
    simp only [decoder]
    congr 1
    funext j
    exact (eval_liftInv J x (t j)).symm
  · intro h i x
    simp only [leftInverseEquation, TermEquation.Holds, Term.eval]
    have hx := congrFun (h x) i
    simp only [decoder] at hx
    rw [← hx]
    congr 1
    funext j
    exact eval_liftInv J x (t j)

/-- The right-inverse equations hold identically iff `decoder J` is a right
inverse of `Θ^{J|σ}`. -/
theorem rightInverseEquations_iff (t : Instance σ k k)
    (J : Interpretation (inverseSignature σ k) A) :
    (∀ i y, (rightInverseEquation t i).Holds J y) ↔
      ∀ y, termMap t (restrictInv J) (decoder J y) = y := by
  have key : ∀ i y, (rightInverseEquation t i).lhs.eval J y =
      termMap t (restrictInv J) (decoder J y) i := by
    intro i y
    simp only [rightInverseEquation, termMap]
    rw [Term.eval_subst, eval_liftInv]
    rfl
  constructor
  · intro h y
    funext i
    have hi := h i y
    simp only [TermEquation.Holds] at hi
    rw [key] at hi
    exact hi
  · intro h i y
    simp only [TermEquation.Holds]
    rw [key]
    exact congrFun (h y) i

/-- If both equation families hold identically for `J`, then the
original-symbol map `Θ^{J|σ}` is bijective (with `decoder J` as a two-sided
inverse). -/
theorem bijective_of_inverseEquations (t : Instance σ k k)
    (J : Interpretation (inverseSignature σ k) A)
    (hl : ∀ i x, (leftInverseEquation t i).Holds J x)
    (hr : ∀ i y, (rightInverseEquation t i).Holds J y) :
    Function.Bijective (termMap t (restrictInv J)) := by
  rw [leftInverseEquations_iff] at hl
  rw [rightInverseEquations_iff] at hr
  exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩

/-- Every bijective interpretation extends to an interpretation of the
extended signature satisfying both equation families, without changing the
original symbols. -/
theorem exists_inverseExtension_of_bijective (t : Instance σ k k)
    (I : Interpretation σ A) (h : Function.Bijective (termMap t I)) :
    ∃ J : Interpretation (inverseSignature σ k) A, restrictInv J = I ∧
      (∀ i x, (leftInverseEquation t i).Holds J x) ∧
      (∀ i y, (rightInverseEquation t i).Holds J y) := by
  obtain ⟨S, hS1, hS2⟩ := Function.bijective_iff_has_inverse.1 h
  refine ⟨extendInv I S, restrictInv_extendInv I S, ?_, ?_⟩
  · rw [leftInverseEquations_iff, restrictInv_extendInv, decoder_extendInv]
    exact hS1
  · rw [rightInverseEquations_iff, restrictInv_extendInv, decoder_extendInv]
    exact hS2

/-- `rem:inverse-extension`: bijectivity of some interpretation of `t` is
equivalent to finite satisfiability of the purely equational inverse-extension
theory, with the inverse symbols quantified freely. -/
theorem exists_inverseExtension_iff (t : Instance σ k k) :
    (∃ J : Interpretation (inverseSignature σ k) A,
        (∀ i x, (leftInverseEquation t i).Holds J x) ∧
        (∀ i y, (rightInverseEquation t i).Holds J y)) ↔
      ∃ I : Interpretation σ A, Function.Bijective (termMap t I) := by
  constructor
  · rintro ⟨J, hl, hr⟩
    exact ⟨restrictInv J, bijective_of_inverseEquations t J hl hr⟩
  · rintro ⟨I, hI⟩
    obtain ⟨J, _, hJ⟩ := exists_inverseExtension_of_bijective t I hI
    exact ⟨J, hJ⟩

end InverseExtension

end Dispersion

end TermCoding
