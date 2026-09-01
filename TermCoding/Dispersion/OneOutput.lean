import TermCoding.Dispersion.Basic
import TermCoding.Dispersion.SquareBijectivity
import Mathlib.Data.Fintype.Pi

/-!
# One output term (V6, remark "Small output dimension: `r = 1`" and
Section 7.1, `BIJ_1`)

A single term `t(x)` can be made surjective onto a finite alphabet with at
least two elements iff `t` contains a variable.

* `prescription_consistent` -- the manuscript's occurrence-based partial
  prescriptions `f^I(π_P(a)) = a` (`P ≠ ∅`) / `c` (`P = ∅`) are consistent:
  if `π_P(a) = π_Q(b)` then the prescribed outputs agree (this covers the
  all-`c` tuple, repeated occurrences of one symbol with different active
  sets, constants, and repeated arguments).
* `routingInterp` -- one total operation table for *every* symbol that
  extends all the prescriptions simultaneously: it returns the unique
  non-`c` input value when the non-`c` inputs agree, and `c` otherwise.
* `eval_routingInterp_slice` -- on the slice where every variable other than
  `x_j` equals `c`, every subterm containing `x_j` evaluates to `x_j` and
  every other subterm to `c` (structural induction).
* `perfectDisp_single_iff` -- `Perfect-Disp_1(t) ⇔ t contains a variable`.
* `bij_one_iff` -- `BIJ_1(t) ⇔ x occurs in t` (Section 7.1).
-/

namespace TermCoding

namespace Dispersion

universe uSym uAlpha

variable {σ : Signature.{uSym}} {A : Type uAlpha}

/-! ### The manuscript's partial prescriptions and their consistency -/

/-- `π_P(a)`: the tuple with `a` at the active positions `P` and `c`
elsewhere. -/
def activeTuple {q : Nat} (P : Finset (Fin q)) (a c : A) : Fin q → A :=
  fun i => if i ∈ P then a else c

/-- The prescribed output: `a` if `P ≠ ∅`, `c` if `P = ∅`. -/
def prescribed {q : Nat} (P : Finset (Fin q)) (a c : A) : A :=
  if P = ∅ then c else a

/-- Consistency of the prescriptions: equal active tuples receive equal
prescribed outputs.  Either `P = Q` and `a = b`, or every coordinate is `c`
and both prescriptions return `c`. -/
theorem prescription_consistent {q : Nat} (P Q : Finset (Fin q)) (a b c : A)
    (h : activeTuple P a c = activeTuple Q b c) :
    prescribed P a c = prescribed Q b c := by
  classical
  unfold prescribed
  by_cases hP : P = ∅
  · by_cases hQ : Q = ∅
    · simp [hP, hQ]
    · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hQ
      have := congrFun h i
      simp [activeTuple, hP, hi] at this
      simp [hP, hQ, this]
  · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hP
    by_cases hQ : Q = ∅
    · have := congrFun h i
      simp [activeTuple, hQ, hi] at this
      simp [hP, hQ, this]
    · simp only [hP, hQ, if_false]
      by_cases hiQ : i ∈ Q
      · have := congrFun h i
        simpa [activeTuple, hi, hiQ] using this
      · -- `a = c`, and some `j ∈ Q` gives `b = c`
        have hac := congrFun h i
        simp [activeTuple, hi, hiQ] at hac
        obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hQ
        by_cases hjP : j ∈ P
        · have := congrFun h j
          simpa [activeTuple, hj, hjP] using this
        · have hbc := congrFun h j
          simp [activeTuple, hj, hjP] at hbc
          rw [hac, hbc]

/-! ### One global operation table extending every prescription -/

/-- The slice assignment: `x_j = a`, every other variable `= c`. -/
def sliceAssignment {k : Nat} (j : Fin k) (a c : A) : Fin k → A :=
  fun i => if i = j then a else c

/-- One operation table for all symbols and arities: forward the (unique)
non-`c` input if there is one, otherwise return `c`. -/
noncomputable def routingInterp (c : A) : Interpretation σ A :=
  fun _ input => by
    classical
    exact if h : ∃ p, input p ≠ c then input (Classical.choose h) else c

theorem routingInterp_eq_of_all_eq (c : A) (s : σ.Symbol)
    (input : Fin (σ.arity s) → A) (h : ∀ p, input p = c) :
    routingInterp c s input = c := by
  classical
  unfold routingInterp
  rw [dif_neg]
  push_neg
  exact h

theorem routingInterp_eq_of_mem (c a : A) (s : σ.Symbol)
    (input : Fin (σ.arity s) → A) (hall : ∀ p, input p = a ∨ input p = c)
    (hex : ∃ p, input p = a) (hac : a ≠ c) :
    routingInterp c s input = a := by
  classical
  unfold routingInterp
  have h : ∃ p, input p ≠ c := by
    obtain ⟨p, hp⟩ := hex
    exact ⟨p, by rw [hp]; exact hac⟩
  rw [dif_pos h]
  rcases hall (Classical.choose h) with h1 | h1
  · exact h1
  · exact absurd h1 (Classical.choose_spec h)

/-- On the slice, a subterm containing `x_j` evaluates to `a` and a subterm
not containing `x_j` evaluates to `c`. -/
theorem eval_routingInterp_slice {k : Nat} (j : Fin k) (a c : A) :
    ∀ u : Term σ (Fin k),
      (Term.HasVar j u → u.eval (routingInterp c) (sliceAssignment j a c) = a) ∧
      (¬ Term.HasVar j u → u.eval (routingInterp c) (sliceAssignment j a c) = c)
  | .var v => by
      constructor
      · intro h
        simp only [Term.HasVar] at h
        simp [Term.eval, sliceAssignment, h]
      · intro h
        simp only [Term.HasVar] at h
        simp [Term.eval, sliceAssignment, h]
  | .app s args => by
      have ih := fun p => eval_routingInterp_slice j a c (args p)
      have hall : ∀ p, (args p).eval (routingInterp c) (sliceAssignment j a c) = a ∨
          (args p).eval (routingInterp c) (sliceAssignment j a c) = c := by
        intro p
        by_cases hp : Term.HasVar j (args p)
        · exact Or.inl ((ih p).1 hp)
        · exact Or.inr ((ih p).2 hp)
      constructor
      · intro h
        obtain ⟨p, hp⟩ := h
        simp only [Term.eval]
        by_cases hac : a = c
        · subst hac
          apply routingInterp_eq_of_all_eq
          intro q
          rcases hall q with hq | hq <;> exact hq
        · exact routingInterp_eq_of_mem c a s _ hall ⟨p, (ih p).1 hp⟩ hac
      · intro h
        simp only [Term.eval]
        apply routingInterp_eq_of_all_eq
        intro p
        exact (ih p).2 (fun hp => h ⟨p, hp⟩)

/-- A term containing a variable is surjective under the routing
interpretation (for any alphabet with a chosen point `c`). -/
theorem surjective_of_hasVar {k : Nat} (u : Term σ (Fin k)) (j : Fin k)
    (hj : Term.HasVar j u) (c : A) :
    Function.Surjective (fun x : Fin k → A => u.eval (routingInterp c) x) := by
  intro a
  exact ⟨sliceAssignment j a c, (eval_routingInterp_slice j a c u).1 hj⟩

/-- A ground term has a one-point image, hence is not surjective onto an
alphabet with at least two elements. -/
theorem not_surjective_of_isGround [Fintype A] (hA : 2 ≤ Fintype.card A)
    {k : Nat} (u : Term σ (Fin k)) (hu : Term.IsGround u) (I : Interpretation σ A) :
    ¬ Function.Surjective (fun x : Fin k → A => u.eval I x) := by
  intro h
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card A)
  obtain ⟨x, hx⟩ := h a
  obtain ⟨y, hy⟩ := h b
  apply hab
  rw [← hx, ← hy]
  exact Term.eval_eq_of_isGround I x y u hu

/-- The term map of a one-output instance is the evaluation of its term. -/
theorem termMap_single {k : Nat} (t : Instance σ k 1) (I : Interpretation σ A)
    (x : Fin k → A) : termMap t I x = fun _ => (t 0).eval I x := by
  funext i
  have : i = 0 := Subsingleton.elim i 0
  subst this
  rfl

/-- A one-output instance is surjective iff its term is. -/
theorem surjective_termMap_single_iff {k : Nat} (t : Instance σ k 1)
    (I : Interpretation σ A) :
    Function.Surjective (termMap t I) ↔
      Function.Surjective (fun x : Fin k → A => (t 0).eval I x) := by
  constructor
  · intro h a
    obtain ⟨x, hx⟩ := h (fun _ => a)
    exact ⟨x, congrFun hx 0⟩
  · intro h y
    obtain ⟨x, hx⟩ := h (y 0)
    refine ⟨x, ?_⟩
    rw [termMap_single]
    funext i
    have : i = 0 := Subsingleton.elim i 0
    subst this
    exact hx

/-- `Perfect-Disp_1`: a single term can be made surjective onto some finite
alphabet of size at least two iff it contains a variable; in that case every
such alphabet admits a witness. -/
theorem perfectDisp_single_iff [Fintype σ.Symbol] {k : Nat} (t : Instance σ k 1) :
    PerfectDisp t ↔ ∃ j, Term.HasVar j (t 0) := by
  rw [perfectDisp_iff_fin]
  constructor
  · rintro ⟨n, hn, I, hI⟩
    by_contra hno
    push_neg at hno
    have hground : Term.IsGround (t 0) := Term.isGround_of_not_hasVar (t 0) hno
    exact not_surjective_of_isGround (A := Fin n) (by simpa using hn) (t 0) hground I
      ((surjective_termMap_single_iff t I).1 hI)
  · rintro ⟨j, hj⟩
    refine ⟨2, le_rfl, routingInterp (0 : Fin 2), ?_⟩
    exact (surjective_termMap_single_iff t _).2 (surjective_of_hasVar (t 0) j hj 0)

/-- Section 7.1: `BIJ_1(t)` iff `x` occurs in `t`; a witness then exists on
every finite alphabet with at least two elements. -/
theorem bij_one_iff [Fintype σ.Symbol] (t : Instance σ 1 1) : BIJ t ↔ Term.HasVar 0 (t 0) := by
  rw [← perfectDisp_iff_bij, perfectDisp_single_iff]
  constructor
  · rintro ⟨j, hj⟩
    have : j = 0 := Subsingleton.elim j 0
    subst this
    exact hj
  · intro h
    exact ⟨0, h⟩

/-- Every finite alphabet with at least two elements witnesses `BIJ_1` when
the variable occurs (the routing interpretation makes `t^I = id`). -/
theorem bijective_single_of_hasVar (t : Instance σ 1 1) (h : Term.HasVar 0 (t 0)) (c : A) :
    Function.Bijective (termMap t (routingInterp c)) := by
  have hid : termMap t (routingInterp c) = id := by
    funext x i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    have hx : x = sliceAssignment 0 (x 0) c := by
      funext v
      have : v = 0 := Subsingleton.elim v 0
      subst this
      simp [sliceAssignment]
    rw [termMap_single, hx]
    exact (eval_routingInterp_slice 0 (x 0) c (t 0)).1 h
  rw [hid]
  exact Function.bijective_id

end Dispersion

end TermCoding
