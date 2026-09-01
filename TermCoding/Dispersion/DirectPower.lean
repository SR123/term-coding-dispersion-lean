import TermCoding.Dispersion.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Fintype.Pi

/-!
# Product alphabets and direct powers preserve surjectivity

The product-alphabet construction proves the multiplicative closure of the
perfect-alphabet spectrum in V10.  The earlier direct-power construction is
retained as its equal-factor specialization.

`powerInterp m I` interprets every symbol (of every arity, including
constants) coordinatewise on `A^m = Fin m → A`.

* `eval_powerInterp` -- every term is evaluated coordinatewise (structural
  induction on terms; nested terms, repeated arguments and repeated symbols
  are all handled by the single global table `powerInterp m I`).
* `termMap_powerInterp_eq` -- `Θ^{I^[m]}` is the conjugate of the
  `m`-fold product `Pi.map (fun _ => Θ^I)` by the explicit coordinate
  transposition `Equiv.piComm` between `(A^m)^k` and `(A^k)^m`.
* `surjective_powerInterp` -- surjectivity is preserved.
* `dispN_pow_eq_of_perfect` -- `Disp_{n^m}(t) = (n^m)^r` whenever
  `Disp_n(t) = n^r` (`n ≥ 1`).
-/

namespace TermCoding

namespace Dispersion

universe uSym uVar uAlpha uBeta

variable {σ : Signature.{uSym}} {A : Type uAlpha} {B : Type uBeta}

/-! ### Products of two possibly different alphabets -/

/-- The product of interpretations on two alphabets, coordinatewise in the
two factors. -/
def productInterp (I : Interpretation σ A) (J : Interpretation σ B) :
    Interpretation σ (A × B) :=
  fun s input =>
    (I s (fun p => (input p).1), J s (fun p => (input p).2))

/-- Every term is evaluated factorwise under the product interpretation. -/
theorem eval_productInterp {V : Type uVar} (I : Interpretation σ A)
    (J : Interpretation σ B) (x : V → A × B) :
    ∀ u : Term σ V,
      u.eval (productInterp I J) x =
        (u.eval I (fun v => (x v).1), u.eval J (fun v => (x v).2))
  | .var v => rfl
  | .app s args => by
      simp only [Term.eval, productInterp]
      apply Prod.ext
      · apply congrArg (I s)
        funext p
        exact congrArg Prod.fst (eval_productInterp I J x (args p))
      · apply congrArg (J s)
        funext p
        exact congrArg Prod.snd (eval_productInterp I J x (args p))

/-- The term map of a product interpretation is the product of the two term
maps, after the canonical rearrangement of coordinates. -/
theorem termMap_productInterp {k r : Nat} (t : Instance σ k r)
    (I : Interpretation σ A) (J : Interpretation σ B) (x : Fin k → A × B) :
    termMap t (productInterp I J) x =
      fun i => (termMap t I (fun v => (x v).1) i,
        termMap t J (fun v => (x v).2) i) := by
  funext i
  exact eval_productInterp I J x (t i)

/-- Product alphabets preserve surjectivity. -/
theorem surjective_productInterp {k r : Nat} (t : Instance σ k r)
    (I : Interpretation σ A) (J : Interpretation σ B)
    (hI : Function.Surjective (termMap t I))
    (hJ : Function.Surjective (termMap t J)) :
    Function.Surjective (termMap t (productInterp I J)) := by
  intro y
  obtain ⟨xA, hxA⟩ := hI (fun i => (y i).1)
  obtain ⟨xB, hxB⟩ := hJ (fun i => (y i).2)
  refine ⟨fun v => (xA v, xB v), ?_⟩
  rw [termMap_productInterp]
  funext i
  exact Prod.ext (congrFun hxA i) (congrFun hxB i)

/-- Numerical form of multiplicative closure of the perfect-alphabet
spectrum. -/
theorem dispN_mul_eq_of_perfect [Fintype σ.Symbol] {k r : Nat}
    (t : Instance σ k r) {a b : Nat} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hA : dispN t a = a ^ r) (hB : dispN t b = b ^ r) :
    dispN t (a * b) = (a * b) ^ r := by
  obtain ⟨I, hI⟩ := (dispN_eq_pow_iff t ha).1 hA
  obtain ⟨J, hJ⟩ := (dispN_eq_pow_iff t hb).1 hB
  haveI : NeZero a := ⟨by omega⟩
  haveI : NeZero b := ⟨by omega⟩
  have hsurj := surjective_productInterp t I J hI hJ
  have h := (exists_surjective_iff_dispN (A := Fin a × Fin b) t).1 ⟨_, hsurj⟩
  simpa using h

/-- The coordinatewise interpretation on the product alphabet `Fin m → A`. -/
def powerInterp (m : Nat) (I : Interpretation σ A) : Interpretation σ (Fin m → A) :=
  fun s input j => I s (fun p => input p j)

/-- Every term is evaluated coordinatewise under the coordinatewise
interpretation. -/
theorem eval_powerInterp {V : Type uVar} (m : Nat) (I : Interpretation σ A)
    (x : V → (Fin m → A)) :
    ∀ u : Term σ V, u.eval (powerInterp m I) x = fun j => u.eval I (fun v => x v j)
  | .var v => rfl
  | .app s args => by
      funext j
      simp only [Term.eval, powerInterp]
      congr 1
      funext p
      exact congrFun (eval_powerInterp m I x (args p)) j

/-- The term map on the product alphabet, computed coordinatewise. -/
theorem termMap_powerInterp {k r : Nat} (m : Nat) (t : Instance σ k r)
    (I : Interpretation σ A) (x : Fin k → (Fin m → A)) :
    termMap t (powerInterp m I) x = fun i j => termMap t I (fun v => x v j) i := by
  funext i j
  exact congrFun (eval_powerInterp m I x (t i)) j

/-- The coordinate transposition `(A^m)^k ≃ (A^k)^m` (`Equiv.piComm`). -/
def transpose (k m : Nat) : (Fin k → (Fin m → A)) ≃ (Fin m → (Fin k → A)) :=
  Equiv.piComm (fun _ _ => A)

/-- `Θ^{I^[m]}` is, after the canonical rearrangement of coordinates, the
direct product of `m` copies of `Θ^I`. -/
theorem termMap_powerInterp_eq {k r : Nat} (m : Nat) (t : Instance σ k r)
    (I : Interpretation σ A) :
    termMap t (powerInterp m I) =
      (transpose r m).symm ∘ Pi.map (fun _ : Fin m => termMap t I) ∘ transpose k m := by
  funext x i j
  rw [termMap_powerInterp]
  rfl

/-- `lem:direct-power`: a direct power of a surjective interpretation is
surjective. -/
theorem surjective_powerInterp {k r : Nat} (m : Nat) (t : Instance σ k r)
    (I : Interpretation σ A) (h : Function.Surjective (termMap t I)) :
    Function.Surjective (termMap t (powerInterp m I)) := by
  rw [termMap_powerInterp_eq]
  exact (transpose r m).symm.surjective.comp
    ((Function.Surjective.piMap (fun _ => h)).comp (transpose k m).surjective)

/-- Numerical form: perfect dispersion at size `n ≥ 1` gives perfect
dispersion at every size `n^m`. -/
theorem dispN_pow_eq_of_perfect [Fintype σ.Symbol] {k r : Nat} (t : Instance σ k r)
    {n : Nat} (hn : 1 ≤ n) (h : dispN t n = n ^ r) (m : Nat) :
    dispN t (n ^ m) = (n ^ m) ^ r := by
  obtain ⟨I, hI⟩ := (dispN_eq_pow_iff t hn).1 h
  haveI : NeZero n := ⟨by omega⟩
  have hsurj := surjective_powerInterp m t I hI
  have h1 := (exists_surjective_iff_dispN (A := Fin m → Fin n) t).1 ⟨_, hsurj⟩
  simpa [Fintype.card_fun, Fintype.card_fin] using h1

end Dispersion

end TermCoding
