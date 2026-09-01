import TermCoding.Terms
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finite.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Order.Basic

/-!
# Dispersion instances (Paper 2, Section 5.1 and Section 6)

This module fixes the objects of the corrected V6 manuscript
(`def:dispersion-multisorted`, `def:decision-problems`, `def:bij3`,
`def:instance-size`) on top of the Paper 1 term syntax.

* `Instance σ k r` -- a tuple of `r` output terms in the input variables
  `x_1, …, x_k` (`Fin k`), over a single-sorted signature `σ`.
* `termMap t I` -- the induced map `Θ^I : A^k → A^r`.  This is the same
  function as `Examples.Dispersion.termMap` of Paper 1 (see
  `TermCoding.Dispersion.Paper1Bridge`).
* `imageCard t I` -- `|Im Θ^I|`.
* `disp A t` -- `Disp_A(t) = max_I |Im Θ^I|`, maximised over *all*
  interpretations of the original signature on the finite alphabet `A`.
* `dispN t n` -- the numerical `Disp_n(t) := Disp_{Fin n}(t)`.

The alphabet is an arbitrary finite type; the manuscript's identification
of a size-`n` alphabet with `[n]` is justified by `disp_congr_equiv`
(dispersion depends only on the cardinality of the alphabet).

Nothing in this file depends on the 2019 max-flow theorem.
-/

namespace TermCoding

universe uSym uVar uWar uAlpha uBeta

namespace Term

/-- Rename variables in a term. -/
def mapVar {σ : Signature.{uSym}} {V : Type uVar} {W : Type uWar} (f : V → W) :
    Term σ V → Term σ W
  | .var v => .var (f v)
  | .app s args => .app s (fun p => mapVar f (args p))

/-- Evaluation after renaming is evaluation of the renamed assignment. -/
theorem eval_mapVar {σ : Signature.{uSym}} {V : Type uVar} {W : Type uWar}
    {A : Type uAlpha} (f : V → W) (I : Interpretation σ A) (x : Assignment W A) :
    ∀ t : Term σ V, (mapVar f t).eval I x = t.eval I (fun v => x (f v))
  | .var v => rfl
  | .app s args => by
      simp only [mapVar, eval]
      congr 1
      funext p
      exact eval_mapVar f I x (args p)

/-- Simultaneous substitution of terms for variables. -/
def subst {σ : Signature.{uSym}} {V : Type uVar} {W : Type uWar}
    (θ : V → Term σ W) : Term σ V → Term σ W
  | .var v => θ v
  | .app s args => .app s (fun p => subst θ (args p))

/-- The substitution lemma: evaluating `t[θ]` is evaluating `t` at the
values of the substituted terms. -/
theorem eval_subst {σ : Signature.{uSym}} {V : Type uVar} {W : Type uWar}
    {A : Type uAlpha} (θ : V → Term σ W) (I : Interpretation σ A)
    (x : Assignment W A) :
    ∀ t : Term σ V, (subst θ t).eval I x = t.eval I (fun v => (θ v).eval I x)
  | .var v => rfl
  | .app s args => by
      simp only [subst, eval]
      congr 1
      funext p
      exact eval_subst θ I x (args p)

/-- Number of symbol occurrences (variables and function symbols) in a term;
the node count of its syntax tree (`def:instance-size`). -/
def size {σ : Signature.{uSym}} {V : Type uVar} : Term σ V → Nat
  | .var _ => 1
  | .app s args => 1 + ∑ p : Fin (σ.arity s), size (args p)

theorem one_le_size {σ : Signature.{uSym}} {V : Type uVar} :
    ∀ t : Term σ V, 1 ≤ t.size
  | .var _ => le_rfl
  | .app _ _ => by simp only [size]; omega

/-- A term contains the variable `v`. -/
def HasVar {σ : Signature.{uSym}} {V : Type uVar} (v : V) : Term σ V → Prop
  | .var w => w = v
  | .app _ args => ∃ p, HasVar v (args p)

/-- A term is ground (contains no variable at all). -/
def IsGround {σ : Signature.{uSym}} {V : Type uVar} : Term σ V → Prop
  | .var _ => False
  | .app _ args => ∀ p, IsGround (args p)

theorem not_hasVar_of_isGround {σ : Signature.{uSym}} {V : Type uVar} :
    ∀ t : Term σ V, IsGround t → ∀ v, ¬ HasVar v t
  | .var _, h => fun _ hv => h
  | .app _ args, h => fun v hv => by
      obtain ⟨p, hp⟩ := hv
      exact not_hasVar_of_isGround (args p) (h p) v hp

theorem isGround_of_not_hasVar {σ : Signature.{uSym}} {V : Type uVar} :
    ∀ t : Term σ V, (∀ v, ¬ HasVar v t) → IsGround t
  | .var w, h => h w rfl
  | .app _ args, h => fun p =>
      isGround_of_not_hasVar (args p) (fun v hv => h v ⟨p, hv⟩)

/-- A ground term evaluates to the same value under every assignment. -/
theorem eval_eq_of_isGround {σ : Signature.{uSym}} {V : Type uVar}
    {A : Type uAlpha} (I : Interpretation σ A) (x y : Assignment V A) :
    ∀ t : Term σ V, IsGround t → t.eval I x = t.eval I y
  | .var _, h => absurd h id
  | .app s args, h => by
      simp only [eval]
      congr 1
      funext p
      exact eval_eq_of_isGround I x y (args p) (h p)

/-- Evaluation only depends on the values of the variables occurring in the
term. -/
theorem eval_congr_of_hasVar {σ : Signature.{uSym}} {V : Type uVar}
    {A : Type uAlpha} (I : Interpretation σ A) (x y : Assignment V A) :
    ∀ t : Term σ V, (∀ v, HasVar v t → x v = y v) → t.eval I x = t.eval I y
  | .var v, h => h v rfl
  | .app s args, h => by
      simp only [eval]
      congr 1
      funext p
      exact eval_congr_of_hasVar I x y (args p) (fun v hv => h v ⟨p, hv⟩)

end Term

namespace Dispersion

/-- `def:dispersion-multisorted`: a single-sorted dispersion instance with
`k` input variables and `r` output terms. -/
abbrev Instance (σ : Signature.{uSym}) (k r : Nat) := Fin r → Term σ (Fin k)

/-- The induced term map `Θ^I : A^k → A^r`. -/
def termMap {σ : Signature.{uSym}} {A : Type uAlpha} {k r : Nat}
    (t : Instance σ k r) (I : Interpretation σ A) :
    (Fin k → A) → (Fin r → A) :=
  fun x i => (t i).eval I x

/-- `|Im Θ^I|`. -/
noncomputable def imageCard {σ : Signature.{uSym}} {A : Type uAlpha} {k r : Nat}
    (t : Instance σ k r) (I : Interpretation σ A) : Nat :=
  Nat.card (Set.range (termMap t I))

/-- Interpretations of a finite signature on a finite alphabet form a finite
type.  (Identical to the Paper 1 instance `TermSystem.interpretationFintype`.) -/
noncomputable instance interpretationFintype {σ : Signature.{uSym}}
    {A : Type uAlpha} [Fintype σ.Symbol] [Fintype A] :
    Fintype (Interpretation σ A) :=
  Fintype.ofFinite _

/-- `Disp_A(t) := max_I |Im Θ^I|`, the maximum over every interpretation of
the original signature `σ` on the finite alphabet `A`. -/
noncomputable def disp {σ : Signature.{uSym}} [Fintype σ.Symbol]
    (A : Type uAlpha) [Fintype A] {k r : Nat} (t : Instance σ k r) : Nat :=
  (Finset.univ : Finset (Interpretation σ A)).sup (fun I => imageCard t I)

/-- The numerical dispersion `Disp_n(t)` at alphabet size `n`. -/
noncomputable def dispN {σ : Signature.{uSym}} [Fintype σ.Symbol] {k r : Nat}
    (t : Instance σ k r) (n : Nat) : Nat :=
  disp (Fin n) t

section ImageCard

variable {σ : Signature.{uSym}} {A : Type uAlpha} {k r : Nat}

theorem imageCard_eq_card_image [Fintype A] [DecidableEq A]
    (t : Instance σ k r) (I : Interpretation σ A) :
    imageCard t I = (Finset.univ.image (termMap t I)).card := by
  classical
  unfold imageCard
  rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
  congr 1
  ext y
  simp [Finset.mem_image]

/-- The image of `Θ^I` has at most `|A|^r` elements. -/
theorem imageCard_le_pow [Fintype A] (t : Instance σ k r)
    (I : Interpretation σ A) : imageCard t I ≤ Fintype.card A ^ r := by
  classical
  rw [imageCard_eq_card_image]
  calc (Finset.univ.image (termMap t I)).card
      ≤ (Finset.univ : Finset (Fin r → A)).card := Finset.card_le_univ _
    _ = Fintype.card A ^ r := by simp

/-- The image of `Θ^I` has at most `|A|^k` elements (`rem:k-less-r`). -/
theorem imageCard_le_pow_dom [Fintype A] (t : Instance σ k r)
    (I : Interpretation σ A) : imageCard t I ≤ Fintype.card A ^ k := by
  classical
  rw [imageCard_eq_card_image]
  calc (Finset.univ.image (termMap t I)).card
      ≤ (Finset.univ : Finset (Fin k → A)).card := Finset.card_image_le
    _ = Fintype.card A ^ k := by simp

/-- `|Im Θ^I| = |A|^r` exactly when `Θ^I` is surjective. -/
theorem imageCard_eq_pow_iff [Fintype A] (t : Instance σ k r)
    (I : Interpretation σ A) :
    imageCard t I = Fintype.card A ^ r ↔ Function.Surjective (termMap t I) := by
  classical
  rw [imageCard_eq_card_image]
  have hcard : Fintype.card A ^ r = Fintype.card (Fin r → A) := by
    simp
  rw [hcard, Finset.card_eq_iff_eq_univ]
  constructor
  · intro h y
    have hy : y ∈ Finset.univ.image (termMap t I) := by
      rw [h]; exact Finset.mem_univ y
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hy
    exact ⟨x, hx⟩
  · intro h
    exact Finset.image_univ_of_surjective h

/-- On a square instance over a finite alphabet, surjectivity and bijectivity
of `Θ^I` coincide (`lem:square-perfect-equals-bij`, (ii) ⇔ (iii)). -/
theorem surjective_iff_bijective_square [Finite A] (t : Instance σ k k)
    (I : Interpretation σ A) :
    Function.Surjective (termMap t I) ↔ Function.Bijective (termMap t I) := by
  constructor
  · intro h
    exact ⟨(Finite.injective_iff_surjective).2 h, h⟩
  · exact fun h => h.2

/-- Injectivity and surjectivity coincide on square instances over a finite
alphabet. -/
theorem injective_iff_surjective_square [Finite A] (t : Instance σ k k)
    (I : Interpretation σ A) :
    Function.Injective (termMap t I) ↔ Function.Surjective (termMap t I) :=
  Finite.injective_iff_surjective

end ImageCard

section Disp

variable {σ : Signature.{uSym}} [Fintype σ.Symbol] {A : Type uAlpha} [Fintype A]
  {k r : Nat}

theorem imageCard_le_disp (t : Instance σ k r) (I : Interpretation σ A) :
    imageCard t I ≤ disp A t :=
  Finset.le_sup (f := fun I => imageCard t I) (Finset.mem_univ I)

/-- The uniform codomain bound `Disp_A(t) ≤ |A|^r`. -/
theorem disp_le_pow (t : Instance σ k r) : disp A t ≤ Fintype.card A ^ r :=
  Finset.sup_le (fun I _ => imageCard_le_pow t I)

/-- The uniform domain bound `Disp_A(t) ≤ |A|^k`. -/
theorem disp_le_pow_dom (t : Instance σ k r) : disp A t ≤ Fintype.card A ^ k :=
  Finset.sup_le (fun I _ => imageCard_le_pow_dom t I)

/-- On a nonempty finite alphabet the maximum is attained. -/
theorem exists_imageCard_eq_disp [Nonempty A] (t : Instance σ k r) :
    ∃ I : Interpretation σ A, imageCard t I = disp A t := by
  classical
  have hne : (Finset.univ : Finset (Interpretation σ A)).Nonempty := by
    refine ⟨fun _ _ => Classical.choice inferInstance, Finset.mem_univ _⟩
  obtain ⟨I, _, hI⟩ := Finset.exists_mem_eq_sup _ hne (fun I => imageCard t I)
  exact ⟨I, hI.symm⟩

/-- "Perfect dispersion" `Disp_A(t) = |A|^r` is exactly the existence of a
surjective interpretation (`def:decision-problems`, `Perfect-Disp_r`). -/
theorem disp_eq_pow_iff [Nonempty A] (t : Instance σ k r) :
    disp A t = Fintype.card A ^ r ↔
      ∃ I : Interpretation σ A, Function.Surjective (termMap t I) := by
  constructor
  · intro h
    obtain ⟨I, hI⟩ := exists_imageCard_eq_disp (A := A) t
    exact ⟨I, (imageCard_eq_pow_iff t I).1 (hI.trans h)⟩
  · rintro ⟨I, hI⟩
    apply le_antisymm (disp_le_pow t)
    rw [← (imageCard_eq_pow_iff t I).2 hI]
    exact imageCard_le_disp t I

/-- `rem:k-less-r`: with fewer inputs than outputs, perfect dispersion is
impossible on every alphabet of size at least two. -/
theorem disp_lt_pow_of_lt (t : Instance σ k r) (hkr : k < r)
    (hA : 2 ≤ Fintype.card A) : disp A t < Fintype.card A ^ r :=
  lt_of_le_of_lt (disp_le_pow_dom t)
    (Nat.pow_lt_pow_right (by omega) hkr)

end Disp

/-! ### Transport along bijections and embeddings of the alphabet -/

namespace Interpretation

variable {σ : Signature.{uSym}} {A : Type uAlpha} {B : Type uBeta}

/-- Transport an interpretation along a bijection of alphabets. -/
def transport (e : A ≃ B) (I : Interpretation σ A) : Interpretation σ B :=
  fun s input => e (I s (fun p => e.symm (input p)))

/-- Extend an interpretation along an injection of alphabets, decoding
inputs with `Function.invFun` (values outside the image are arbitrary). -/
noncomputable def extend [Nonempty A] (e : A ↪ B) (I : Interpretation σ A) :
    Interpretation σ B :=
  fun s input => e (I s (fun p => Function.invFun e (input p)))

end Interpretation

section Transport

variable {σ : Signature.{uSym}} {A : Type uAlpha} {B : Type uBeta} {k r : Nat}

theorem eval_transport (e : A ≃ B) (I : Interpretation σ A)
    (x : Assignment (Fin k) A) :
    ∀ t : Term σ (Fin k),
      t.eval (Interpretation.transport e I) (fun i => e (x i)) = e (t.eval I x)
  | .var v => rfl
  | .app s args => by
      simp only [Term.eval, Interpretation.transport]
      congr 2
      funext p
      rw [eval_transport e I x (args p), Equiv.symm_apply_apply]

theorem termMap_transport (e : A ≃ B) (t : Instance σ k r)
    (I : Interpretation σ A) (x : Assignment (Fin k) A) :
    termMap t (Interpretation.transport e I) (fun i => e (x i)) =
      fun i => e (termMap t I x i) := by
  funext i
  exact eval_transport e I x (t i)

theorem eval_extend [Nonempty A] (e : A ↪ B) (I : Interpretation σ A)
    (x : Assignment (Fin k) A) :
    ∀ t : Term σ (Fin k),
      t.eval (Interpretation.extend e I) (fun i => e (x i)) = e (t.eval I x)
  | .var v => rfl
  | .app s args => by
      simp only [Term.eval, Interpretation.extend]
      congr 2
      funext p
      rw [eval_extend e I x (args p), Function.leftInverse_invFun e.injective]

theorem termMap_extend [Nonempty A] (e : A ↪ B) (t : Instance σ k r)
    (I : Interpretation σ A) (x : Assignment (Fin k) A) :
    termMap t (Interpretation.extend e I) (fun i => e (x i)) =
      fun i => e (termMap t I x i) := by
  funext i
  exact eval_extend e I x (t i)

/-- Extending the alphabet along an injection can only enlarge the image. -/
theorem imageCard_le_imageCard_extend [Nonempty A] [Finite B] (e : A ↪ B)
    (t : Instance σ k r) (I : Interpretation σ A) :
    imageCard t I ≤ imageCard t (Interpretation.extend e I) := by
  unfold imageCard
  let φ : Set.range (termMap t I) → Set.range (termMap t (Interpretation.extend e I)) :=
    fun y => ⟨fun i => e (y.1 i), by
      obtain ⟨x, hx⟩ := y.2
      exact ⟨fun i => e (x i), by rw [termMap_extend, hx]⟩⟩
  have hφ : Function.Injective φ := by
    intro y₁ y₂ h
    apply Subtype.ext
    funext i
    have := congrArg (fun z => z.1 i) h
    exact e.injective this
  exact Nat.card_le_card_of_injective φ hφ

/-- `Disp` is monotone under injections of nonempty finite alphabets. -/
theorem disp_le_of_embedding [Fintype σ.Symbol] [Fintype A] [Fintype B]
    [Nonempty A] (e : A ↪ B) (t : Instance σ k r) : disp A t ≤ disp B t := by
  apply Finset.sup_le
  intro I _
  exact (imageCard_le_imageCard_extend e t I).trans
    (imageCard_le_disp t (Interpretation.extend e I))

/-- `Disp` depends only on the cardinality of the alphabet.  This justifies
the manuscript's identification of a size-`n` alphabet with `[n]`. -/
theorem disp_congr_equiv [Fintype σ.Symbol] [Fintype A] [Fintype B]
    (e : A ≃ B) (t : Instance σ k r) : disp A t = disp B t := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro I _
    refine le_trans ?_ (imageCard_le_disp t (Interpretation.transport e I))
    unfold imageCard
    let φ : Set.range (termMap t I) → Set.range (termMap t (Interpretation.transport e I)) :=
      fun y => ⟨fun i => e (y.1 i), by
        obtain ⟨x, hx⟩ := y.2
        exact ⟨fun i => e (x i), by rw [termMap_transport, hx]⟩⟩
    have hφ : Function.Injective φ := by
      intro y₁ y₂ h
      apply Subtype.ext
      funext i
      exact e.injective (congrArg (fun z => z.1 i) h)
    exact Nat.card_le_card_of_injective φ hφ
  · apply Finset.sup_le
    intro J _
    refine le_trans ?_ (imageCard_le_disp t (Interpretation.transport e.symm J))
    unfold imageCard
    let φ : Set.range (termMap t J) → Set.range (termMap t (Interpretation.transport e.symm J)) :=
      fun y => ⟨fun i => e.symm (y.1 i), by
        obtain ⟨x, hx⟩ := y.2
        exact ⟨fun i => e.symm (x i), by rw [termMap_transport, hx]⟩⟩
    have hφ : Function.Injective φ := by
      intro y₁ y₂ h
      apply Subtype.ext
      funext i
      exact e.symm.injective (congrArg (fun z => z.1 i) h)
    exact Nat.card_le_card_of_injective φ hφ

/-- `Disp_A(t) = Disp_{|A|}(t)`. -/
theorem disp_eq_dispN [Fintype σ.Symbol] [Fintype A] (t : Instance σ k r) :
    disp A t = dispN t (Fintype.card A) :=
  disp_congr_equiv (Fintype.equivFin A) t

/-- Numerical monotonicity `Disp_n(t) ≤ Disp_m(t)` for `1 ≤ n ≤ m`. -/
theorem dispN_mono [Fintype σ.Symbol] (t : Instance σ k r) {n m : Nat}
    (hn : 1 ≤ n) (hnm : n ≤ m) : dispN t n ≤ dispN t m := by
  haveI : NeZero n := ⟨by omega⟩
  exact disp_le_of_embedding (Fin.castLEEmb hnm) t

theorem dispN_le_pow [Fintype σ.Symbol] (t : Instance σ k r) (n : Nat) :
    dispN t n ≤ n ^ r := by
  simpa using (disp_le_pow (A := Fin n) t)

theorem dispN_le_pow_dom [Fintype σ.Symbol] (t : Instance σ k r) (n : Nat) :
    dispN t n ≤ n ^ k := by
  simpa using (disp_le_pow_dom (A := Fin n) t)

/-- `Disp_n(t) = n^r` iff some interpretation on `Fin n` is surjective
(`n ≥ 1`). -/
theorem dispN_eq_pow_iff [Fintype σ.Symbol] (t : Instance σ k r) {n : Nat}
    (hn : 1 ≤ n) :
    dispN t n = n ^ r ↔
      ∃ I : Interpretation σ (Fin n), Function.Surjective (termMap t I) := by
  haveI : NeZero n := ⟨by omega⟩
  have := disp_eq_pow_iff (A := Fin n) t
  simpa using this

/-- Perfect dispersion on an abstract finite alphabet of size `n` is perfect
dispersion at the numerical size `n` (transport along `Fintype.equivFin`). -/
theorem exists_surjective_iff_dispN [Fintype σ.Symbol] [Fintype A] [Nonempty A]
    (t : Instance σ k r) :
    (∃ I : Interpretation σ A, Function.Surjective (termMap t I)) ↔
      dispN t (Fintype.card A) = Fintype.card A ^ r := by
  rw [← disp_eq_dispN, disp_eq_pow_iff]

end Transport

/-! ### The decision problems of `def:decision-problems` and `def:bij3` -/

section Problems

variable {σ : Signature.{uSym}} [Fintype σ.Symbol] {k r : Nat}

/-- `Fixed-Perfect-Disp(t, n)`: is `Disp_n(t) = n^r`? -/
def PerfectDispAt (t : Instance σ k r) (n : Nat) : Prop := dispN t n = n ^ r

/-- `Perfect-Disp_r(t)` and `Perfect-Disp(t)`: does some alphabet size
`n ≥ 2` give `Disp_n(t) = n^r`?  (The output count `r` is part of the type
of `t`; fixing `r` gives the fixed-parameter version.) -/
def PerfectDisp (t : Instance σ k r) : Prop := ∃ n, 2 ≤ n ∧ dispN t n = n ^ r

/-- The alternative phrasing of `Perfect-Disp_r` in `def:decision-problems`:
some interpretation on some finite set of size at least two is surjective. -/
def SurjectiveWitness (t : Instance σ k r) : Prop :=
  ∃ (A : Type) (_ : Fintype A), 2 ≤ Fintype.card A ∧
    ∃ I : Interpretation σ A, Function.Surjective (termMap t I)

/-- `def:bij3`: square bijectivity `BIJ_k` (and `BIJ` when `k` is part of
the input): some interpretation on some finite set of size at least two makes
`Θ^I : A^k → A^k` bijective. -/
def BIJ (t : Instance σ k k) : Prop :=
  ∃ (A : Type) (_ : Fintype A), 2 ≤ Fintype.card A ∧
    ∃ I : Interpretation σ A, Function.Bijective (termMap t I)

/-- The two phrasings of `Perfect-Disp_r` in `def:decision-problems` agree. -/
theorem perfectDisp_iff_surjectiveWitness (t : Instance σ k r) :
    PerfectDisp t ↔ SurjectiveWitness t := by
  constructor
  · rintro ⟨n, hn, h⟩
    haveI : NeZero n := ⟨by omega⟩
    obtain ⟨I, hI⟩ := (dispN_eq_pow_iff t (by omega)).1 h
    exact ⟨Fin n, inferInstance, by simpa using hn, I, hI⟩
  · rintro ⟨A, _, hA, I, hI⟩
    haveI : Nonempty A := Fintype.card_pos_iff.mp (by omega)
    refine ⟨Fintype.card A, hA, ?_⟩
    exact (exists_surjective_iff_dispN t).1 ⟨I, hI⟩

/-- `PerfectDisp` on `Fin n` alphabets only. -/
theorem perfectDisp_iff_fin (t : Instance σ k r) :
    PerfectDisp t ↔
      ∃ n, 2 ≤ n ∧ ∃ I : Interpretation σ (Fin n),
        Function.Surjective (termMap t I) := by
  constructor
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, (dispN_eq_pow_iff t (by omega)).1 h⟩
  · rintro ⟨n, hn, I, hI⟩
    exact ⟨n, hn, (dispN_eq_pow_iff t (by omega)).2 ⟨I, hI⟩⟩

omit [Fintype σ.Symbol] in
/-- `BIJ` on `Fin n` alphabets only. -/
theorem bij_iff_fin (t : Instance σ k k) :
    BIJ t ↔
      ∃ n, 2 ≤ n ∧ ∃ I : Interpretation σ (Fin n),
        Function.Bijective (termMap t I) := by
  constructor
  · rintro ⟨A, _, hA, I, hI⟩
    refine ⟨Fintype.card A, hA, Interpretation.transport (Fintype.equivFin A) I, ?_⟩
    rw [← surjective_iff_bijective_square, ← injective_iff_surjective_square]
    intro x y hxy
    let e := Fintype.equivFin A
    have hx : x = fun i => e (e.symm (x i)) := by funext i; simp
    have hy : y = fun i => e (e.symm (y i)) := by funext i; simp
    rw [hx, hy, termMap_transport, termMap_transport] at hxy
    have h2 : termMap t I (fun i => e.symm (x i)) = termMap t I (fun i => e.symm (y i)) := by
      funext i
      exact e.injective (congrFun hxy i)
    have h3 := hI.1 h2
    funext i
    have := congrFun h3 i
    simpa using congrArg e this
  · rintro ⟨n, hn, I, hI⟩
    exact ⟨Fin n, inferInstance, by simpa using hn, I, hI⟩

end Problems

/-! ### Syntactic size (`def:instance-size`) -/

/-- `‖t‖`: total number of symbol occurrences in the output terms, plus the
number `r` of output terms. -/
def Instance.size {σ : Signature.{uSym}} {k r : Nat} (t : Instance σ k r) : Nat :=
  (∑ i : Fin r, (t i).size) + r

end Dispersion

end TermCoding
