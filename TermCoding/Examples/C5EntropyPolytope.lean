import Mathlib.Analysis.Convex.Extreme
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic

/-!
# The five-cycle entropy polytope: a non-integer vertex

Formal content of Proposition 7.1 (journal version of Paper 1), which replaced
the former Remark 7.1.  Let `P5` be the set of polymatroid rank functions
`h : 2^[5] → ℝ` (with `h ∅ = 0`, monotone, submodular) satisfying the
five-cycle dependence constraints `h {i, i+1, i+2} = h {i, i+2}` (all indices
mod 5) and the alphabet bounds `h {i} ≤ 1`.  Then

* `hstar S = |S ∪ (S+1)| / 2` lies in `P5` (`hstar_mem`);
* `h [5] ≤ 5/2` for every `h ∈ P5` (`le_five_halves`), with equality at
  `hstar` (`hstar_univ`);
* `hstar` is the **unique** maximiser (`eq_hstar_of_max`);
* hence `hstar` is an extreme point (vertex) of `P5` (`hstar_extreme`);
* `hstar` has non-integer coordinates, e.g. `hstar {0,1} = 3/2`
  (`hstar_pair_not_integer`).

The realisation of `hstar` as the normalised entropy vector of the uniform
distribution on the winning set of the square-alphabet construction is in
`C5EntropyRealisation.lean`.

Author: Claude (Fable 5), 27 August 2026.  Generated in part by
`gen_polytope.py` (the instantiated inequalities); every proof is checked by
Lean.
-/

namespace TermCoding.Examples.C5Entropy

open Finset

/-- Real-valued set functions on the five-element ground set. -/
abbrev SetFn := Finset (Fin 5) → ℝ

/-- `N S = S ∪ (S + 1)`: the ground elements "seen" by the coordinates in `S`
under the square-alphabet construction `X_i = (U_i, U_{i+1})`. -/
def N (S : Finset (Fin 5)) : Finset (Fin 5) := S ∪ S.image (· + 1)

/-- The candidate optimum: half the size of `N S`. -/
noncomputable def hstar : SetFn := fun S => ((N S).card : ℝ) / 2

/-- Polymatroid rank functions: normalised at `∅`, monotone, submodular. -/
structure IsPolymatroid (h : SetFn) : Prop where
  empty : h ∅ = 0
  mono : ∀ S T, S ⊆ T → h S ≤ h T
  submod : ∀ S T, h (S ∪ T) + h (S ∩ T) ≤ h S + h T

/-- The five-cycle functional-dependence constraints `H(X_{i+1} | X_i, X_{i+2}) = 0`. -/
def Dependencies (h : SetFn) : Prop := ∀ i : Fin 5, h {i, i + 1, i + 2} = h {i, i + 2}

/-- Alphabet bounds in base-`n` units: `H(X_i) ≤ log n`. -/
def Normalised (h : SetFn) : Prop := ∀ i : Fin 5, h {i} ≤ 1

/-- The five-cycle entropy polytope. -/
def P5 : Set SetFn := {h | IsPolymatroid h ∧ Dependencies h ∧ Normalised h}

/-! ### `hstar` is a normalised polymatroid satisfying the dependencies -/

theorem N_mono {S T : Finset (Fin 5)} (hST : S ⊆ T) : N S ⊆ N T :=
  Finset.union_subset_union hST (Finset.image_subset_image hST)

theorem N_union (S T : Finset (Fin 5)) : N (S ∪ T) = N S ∪ N T := by
  unfold N
  rw [Finset.image_union]
  ext x
  simp only [Finset.mem_union]
  tauto

theorem N_inter_subset (S T : Finset (Fin 5)) : N (S ∩ T) ⊆ N S ∩ N T :=
  Finset.subset_inter (N_mono Finset.inter_subset_left) (N_mono Finset.inter_subset_right)

theorem hstar_polymatroid : IsPolymatroid hstar where
  empty := by simp [hstar, N]
  mono := by
    intro S T hST
    unfold hstar
    have : (N S).card ≤ (N T).card := Finset.card_le_card (N_mono hST)
    have h' : ((N S).card : ℝ) ≤ (N T).card := by exact_mod_cast this
    linarith
  submod := by
    intro S T
    unfold hstar
    have h1 : (N (S ∪ T)).card + (N (S ∩ T)).card ≤ (N S).card + (N T).card := by
      rw [N_union]
      calc (N S ∪ N T).card + (N (S ∩ T)).card
          ≤ (N S ∪ N T).card + (N S ∩ N T).card :=
            Nat.add_le_add_left (Finset.card_le_card (N_inter_subset S T)) _
        _ = (N S).card + (N T).card := Finset.card_union_add_card_inter _ _
    have h2 : ((N (S ∪ T)).card : ℝ) + (N (S ∩ T)).card ≤ (N S).card + (N T).card := by
      exact_mod_cast h1
    linarith

theorem hstar_dependencies : Dependencies hstar := by
  have key : ∀ i : Fin 5, (N {i, i + 1, i + 2}).card = (N {i, i + 2}).card := by decide
  intro i
  unfold hstar
  rw [key i]

theorem hstar_normalised : Normalised hstar := by
  have key : ∀ i : Fin 5, (N {i}).card = 2 := by decide
  intro i
  unfold hstar
  rw [key i]
  norm_num

theorem hstar_mem : hstar ∈ P5 :=
  ⟨hstar_polymatroid, hstar_dependencies, hstar_normalised⟩

theorem hstar_univ : hstar Finset.univ = 5 / 2 := by
  unfold hstar
  rw [show (N Finset.univ).card = 5 by decide]
  norm_num

theorem hstar_pair : hstar {0, 1} = 3 / 2 := by
  unfold hstar
  rw [show (N {0, 1}).card = 3 by decide]
  norm_num

/-! ### Instantiation helpers -/

theorem submod_at (h : SetFn) (hp : IsPolymatroid h) {S T U I : Finset (Fin 5)}
    (hU : S ∪ T = U) (hI : S ∩ T = I) : h U + h I ≤ h S + h T := by
  have := hp.submod S T
  rwa [hU, hI] at this

theorem dep_at (h : SetFn) (hd : Dependencies h) (i : Fin 5) {A B : Finset (Fin 5)}
    (hA : ({i, i + 1, i + 2} : Finset (Fin 5)) = A) (hB : ({i, i + 2} : Finset (Fin 5)) = B) :
    h A = h B := by
  have := hd i
  rwa [hA, hB] at this

/-! ### The upper bound `h [5] ≤ 5/2` (the chain of Theorem 8.1) -/

theorem le_five_halves (h : SetFn) (hP : h ∈ P5) : h Finset.univ ≤ 5 / 2 := by
  obtain ⟨hpoly, hdep, hnorm⟩ := hP

  have e0 := hpoly.empty
  have s1 := submod_at h hpoly (S := {0, 1, 2, 3}) (T := {0, 3, 4}) (U := Finset.univ) (I := {0, 3}) (by decide) (by decide)
  have s2 := submod_at h hpoly (S := {0, 1, 3}) (T := {1, 2, 3}) (U := {0, 1, 2, 3}) (I := {1, 3}) (by decide) (by decide)
  have s3 := submod_at h hpoly (S := {0, 1}) (T := {3}) (U := {0, 1, 3}) (I := ∅) (by decide) (by decide)
  have s4 := submod_at h hpoly (S := {0, 1, 2, 4}) (T := {2, 3, 4}) (U := Finset.univ) (I := {2, 4}) (by decide) (by decide)
  have s5 := submod_at h hpoly (S := {0, 1, 2}) (T := {0, 1, 4}) (U := {0, 1, 2, 4}) (I := {0, 1}) (by decide) (by decide)
  have s6 := submod_at h hpoly (S := {1}) (T := {4}) (U := {1, 4}) (I := ∅) (by decide) (by decide)
  have s7 := submod_at h hpoly (S := {0}) (T := {2}) (U := {0, 2}) (I := ∅) (by decide) (by decide)
  have d0 := dep_at h hdep 0 (A := {0, 1, 2}) (B := {0, 2}) (by decide) (by decide)
  have d1 := dep_at h hdep 1 (A := {1, 2, 3}) (B := {1, 3}) (by decide) (by decide)
  have d2 := dep_at h hdep 2 (A := {2, 3, 4}) (B := {2, 4}) (by decide) (by decide)
  have d3 := dep_at h hdep 3 (A := {0, 3, 4}) (B := {0, 3}) (by decide) (by decide)
  have d4 := dep_at h hdep 4 (A := {0, 1, 4}) (B := {1, 4}) (by decide) (by decide)
  have n0 := hnorm 0
  have n1 := hnorm 1
  have n2 := hnorm 2
  have n3 := hnorm 3
  have n4 := hnorm 4
  linarith

/-! ### Pinning lemmas: equality in the chain (and its rotations) forces the coordinates -/

theorem pin_0 (h : SetFn) (hpoly : IsPolymatroid h) (hdep : Dependencies h)
    (hnorm : Normalised h) (hmax : h Finset.univ = 5 / 2) :
      h {0} = 1 ∧
      h {1} = 1 ∧
      h {2} = 1 ∧
      h {3} = 1 ∧
      h {4} = 1 ∧
      h {0, 1} = 3 / 2 ∧
      h {0, 2} = 2 ∧
      h {1, 4} = 2 ∧
      h {0, 1, 3} = 5 / 2 ∧
      h {0, 1, 2, 3} = 5 / 2 ∧
      h {0, 1, 2, 4} = 5 / 2 ∧
      h {0, 1, 2} = 2 ∧
      h {0, 1, 4} = 2 := by
  have e0 := hpoly.empty
  have s1 := submod_at h hpoly (S := {0, 1, 2, 3}) (T := {0, 3, 4}) (U := Finset.univ) (I := {0, 3}) (by decide) (by decide)
  have s2 := submod_at h hpoly (S := {0, 1, 3}) (T := {1, 2, 3}) (U := {0, 1, 2, 3}) (I := {1, 3}) (by decide) (by decide)
  have s3 := submod_at h hpoly (S := {0, 1}) (T := {3}) (U := {0, 1, 3}) (I := ∅) (by decide) (by decide)
  have s4 := submod_at h hpoly (S := {0, 1, 2, 4}) (T := {2, 3, 4}) (U := Finset.univ) (I := {2, 4}) (by decide) (by decide)
  have s5 := submod_at h hpoly (S := {0, 1, 2}) (T := {0, 1, 4}) (U := {0, 1, 2, 4}) (I := {0, 1}) (by decide) (by decide)
  have s6 := submod_at h hpoly (S := {1}) (T := {4}) (U := {1, 4}) (I := ∅) (by decide) (by decide)
  have s7 := submod_at h hpoly (S := {0}) (T := {2}) (U := {0, 2}) (I := ∅) (by decide) (by decide)
  have d0 := dep_at h hdep 0 (A := {0, 1, 2}) (B := {0, 2}) (by decide) (by decide)
  have d1 := dep_at h hdep 1 (A := {1, 2, 3}) (B := {1, 3}) (by decide) (by decide)
  have d2 := dep_at h hdep 2 (A := {2, 3, 4}) (B := {2, 4}) (by decide) (by decide)
  have d3 := dep_at h hdep 3 (A := {0, 3, 4}) (B := {0, 3}) (by decide) (by decide)
  have d4 := dep_at h hdep 4 (A := {0, 1, 4}) (B := {1, 4}) (by decide) (by decide)
  have n0 := hnorm 0
  have n1 := hnorm 1
  have n2 := hnorm 2
  have n3 := hnorm 3
  have n4 := hnorm 4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem pin_1 (h : SetFn) (hpoly : IsPolymatroid h) (hdep : Dependencies h)
    (hnorm : Normalised h) (hmax : h Finset.univ = 5 / 2) :
      h {1} = 1 ∧
      h {2} = 1 ∧
      h {3} = 1 ∧
      h {4} = 1 ∧
      h {0} = 1 ∧
      h {1, 2} = 3 / 2 ∧
      h {1, 3} = 2 ∧
      h {0, 2} = 2 ∧
      h {1, 2, 4} = 5 / 2 ∧
      h {1, 2, 3, 4} = 5 / 2 ∧
      h {0, 1, 2, 3} = 5 / 2 ∧
      h {1, 2, 3} = 2 ∧
      h {0, 1, 2} = 2 := by
  have e0 := hpoly.empty
  have s1 := submod_at h hpoly (S := {1, 2, 3, 4}) (T := {0, 1, 4}) (U := Finset.univ) (I := {1, 4}) (by decide) (by decide)
  have s2 := submod_at h hpoly (S := {1, 2, 4}) (T := {2, 3, 4}) (U := {1, 2, 3, 4}) (I := {2, 4}) (by decide) (by decide)
  have s3 := submod_at h hpoly (S := {1, 2}) (T := {4}) (U := {1, 2, 4}) (I := ∅) (by decide) (by decide)
  have s4 := submod_at h hpoly (S := {0, 1, 2, 3}) (T := {0, 3, 4}) (U := Finset.univ) (I := {0, 3}) (by decide) (by decide)
  have s5 := submod_at h hpoly (S := {1, 2, 3}) (T := {0, 1, 2}) (U := {0, 1, 2, 3}) (I := {1, 2}) (by decide) (by decide)
  have s6 := submod_at h hpoly (S := {2}) (T := {0}) (U := {0, 2}) (I := ∅) (by decide) (by decide)
  have s7 := submod_at h hpoly (S := {1}) (T := {3}) (U := {1, 3}) (I := ∅) (by decide) (by decide)
  have d0 := dep_at h hdep 0 (A := {0, 1, 2}) (B := {0, 2}) (by decide) (by decide)
  have d1 := dep_at h hdep 1 (A := {1, 2, 3}) (B := {1, 3}) (by decide) (by decide)
  have d2 := dep_at h hdep 2 (A := {2, 3, 4}) (B := {2, 4}) (by decide) (by decide)
  have d3 := dep_at h hdep 3 (A := {0, 3, 4}) (B := {0, 3}) (by decide) (by decide)
  have d4 := dep_at h hdep 4 (A := {0, 1, 4}) (B := {1, 4}) (by decide) (by decide)
  have n0 := hnorm 0
  have n1 := hnorm 1
  have n2 := hnorm 2
  have n3 := hnorm 3
  have n4 := hnorm 4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem pin_2 (h : SetFn) (hpoly : IsPolymatroid h) (hdep : Dependencies h)
    (hnorm : Normalised h) (hmax : h Finset.univ = 5 / 2) :
      h {2} = 1 ∧
      h {3} = 1 ∧
      h {4} = 1 ∧
      h {0} = 1 ∧
      h {1} = 1 ∧
      h {2, 3} = 3 / 2 ∧
      h {2, 4} = 2 ∧
      h {1, 3} = 2 ∧
      h {0, 2, 3} = 5 / 2 ∧
      h {0, 2, 3, 4} = 5 / 2 ∧
      h {1, 2, 3, 4} = 5 / 2 ∧
      h {2, 3, 4} = 2 ∧
      h {1, 2, 3} = 2 := by
  have e0 := hpoly.empty
  have s1 := submod_at h hpoly (S := {0, 2, 3, 4}) (T := {0, 1, 2}) (U := Finset.univ) (I := {0, 2}) (by decide) (by decide)
  have s2 := submod_at h hpoly (S := {0, 2, 3}) (T := {0, 3, 4}) (U := {0, 2, 3, 4}) (I := {0, 3}) (by decide) (by decide)
  have s3 := submod_at h hpoly (S := {2, 3}) (T := {0}) (U := {0, 2, 3}) (I := ∅) (by decide) (by decide)
  have s4 := submod_at h hpoly (S := {1, 2, 3, 4}) (T := {0, 1, 4}) (U := Finset.univ) (I := {1, 4}) (by decide) (by decide)
  have s5 := submod_at h hpoly (S := {2, 3, 4}) (T := {1, 2, 3}) (U := {1, 2, 3, 4}) (I := {2, 3}) (by decide) (by decide)
  have s6 := submod_at h hpoly (S := {3}) (T := {1}) (U := {1, 3}) (I := ∅) (by decide) (by decide)
  have s7 := submod_at h hpoly (S := {2}) (T := {4}) (U := {2, 4}) (I := ∅) (by decide) (by decide)
  have d0 := dep_at h hdep 0 (A := {0, 1, 2}) (B := {0, 2}) (by decide) (by decide)
  have d1 := dep_at h hdep 1 (A := {1, 2, 3}) (B := {1, 3}) (by decide) (by decide)
  have d2 := dep_at h hdep 2 (A := {2, 3, 4}) (B := {2, 4}) (by decide) (by decide)
  have d3 := dep_at h hdep 3 (A := {0, 3, 4}) (B := {0, 3}) (by decide) (by decide)
  have d4 := dep_at h hdep 4 (A := {0, 1, 4}) (B := {1, 4}) (by decide) (by decide)
  have n0 := hnorm 0
  have n1 := hnorm 1
  have n2 := hnorm 2
  have n3 := hnorm 3
  have n4 := hnorm 4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem pin_3 (h : SetFn) (hpoly : IsPolymatroid h) (hdep : Dependencies h)
    (hnorm : Normalised h) (hmax : h Finset.univ = 5 / 2) :
      h {3} = 1 ∧
      h {4} = 1 ∧
      h {0} = 1 ∧
      h {1} = 1 ∧
      h {2} = 1 ∧
      h {3, 4} = 3 / 2 ∧
      h {0, 3} = 2 ∧
      h {2, 4} = 2 ∧
      h {1, 3, 4} = 5 / 2 ∧
      h {0, 1, 3, 4} = 5 / 2 ∧
      h {0, 2, 3, 4} = 5 / 2 ∧
      h {0, 3, 4} = 2 ∧
      h {2, 3, 4} = 2 := by
  have e0 := hpoly.empty
  have s1 := submod_at h hpoly (S := {0, 1, 3, 4}) (T := {1, 2, 3}) (U := Finset.univ) (I := {1, 3}) (by decide) (by decide)
  have s2 := submod_at h hpoly (S := {1, 3, 4}) (T := {0, 1, 4}) (U := {0, 1, 3, 4}) (I := {1, 4}) (by decide) (by decide)
  have s3 := submod_at h hpoly (S := {3, 4}) (T := {1}) (U := {1, 3, 4}) (I := ∅) (by decide) (by decide)
  have s4 := submod_at h hpoly (S := {0, 2, 3, 4}) (T := {0, 1, 2}) (U := Finset.univ) (I := {0, 2}) (by decide) (by decide)
  have s5 := submod_at h hpoly (S := {0, 3, 4}) (T := {2, 3, 4}) (U := {0, 2, 3, 4}) (I := {3, 4}) (by decide) (by decide)
  have s6 := submod_at h hpoly (S := {4}) (T := {2}) (U := {2, 4}) (I := ∅) (by decide) (by decide)
  have s7 := submod_at h hpoly (S := {3}) (T := {0}) (U := {0, 3}) (I := ∅) (by decide) (by decide)
  have d0 := dep_at h hdep 0 (A := {0, 1, 2}) (B := {0, 2}) (by decide) (by decide)
  have d1 := dep_at h hdep 1 (A := {1, 2, 3}) (B := {1, 3}) (by decide) (by decide)
  have d2 := dep_at h hdep 2 (A := {2, 3, 4}) (B := {2, 4}) (by decide) (by decide)
  have d3 := dep_at h hdep 3 (A := {0, 3, 4}) (B := {0, 3}) (by decide) (by decide)
  have d4 := dep_at h hdep 4 (A := {0, 1, 4}) (B := {1, 4}) (by decide) (by decide)
  have n0 := hnorm 0
  have n1 := hnorm 1
  have n2 := hnorm 2
  have n3 := hnorm 3
  have n4 := hnorm 4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem pin_4 (h : SetFn) (hpoly : IsPolymatroid h) (hdep : Dependencies h)
    (hnorm : Normalised h) (hmax : h Finset.univ = 5 / 2) :
      h {4} = 1 ∧
      h {0} = 1 ∧
      h {1} = 1 ∧
      h {2} = 1 ∧
      h {3} = 1 ∧
      h {0, 4} = 3 / 2 ∧
      h {1, 4} = 2 ∧
      h {0, 3} = 2 ∧
      h {0, 2, 4} = 5 / 2 ∧
      h {0, 1, 2, 4} = 5 / 2 ∧
      h {0, 1, 3, 4} = 5 / 2 ∧
      h {0, 1, 4} = 2 ∧
      h {0, 3, 4} = 2 := by
  have e0 := hpoly.empty
  have s1 := submod_at h hpoly (S := {0, 1, 2, 4}) (T := {2, 3, 4}) (U := Finset.univ) (I := {2, 4}) (by decide) (by decide)
  have s2 := submod_at h hpoly (S := {0, 2, 4}) (T := {0, 1, 2}) (U := {0, 1, 2, 4}) (I := {0, 2}) (by decide) (by decide)
  have s3 := submod_at h hpoly (S := {0, 4}) (T := {2}) (U := {0, 2, 4}) (I := ∅) (by decide) (by decide)
  have s4 := submod_at h hpoly (S := {0, 1, 3, 4}) (T := {1, 2, 3}) (U := Finset.univ) (I := {1, 3}) (by decide) (by decide)
  have s5 := submod_at h hpoly (S := {0, 1, 4}) (T := {0, 3, 4}) (U := {0, 1, 3, 4}) (I := {0, 4}) (by decide) (by decide)
  have s6 := submod_at h hpoly (S := {0}) (T := {3}) (U := {0, 3}) (I := ∅) (by decide) (by decide)
  have s7 := submod_at h hpoly (S := {4}) (T := {1}) (U := {1, 4}) (I := ∅) (by decide) (by decide)
  have d0 := dep_at h hdep 0 (A := {0, 1, 2}) (B := {0, 2}) (by decide) (by decide)
  have d1 := dep_at h hdep 1 (A := {1, 2, 3}) (B := {1, 3}) (by decide) (by decide)
  have d2 := dep_at h hdep 2 (A := {2, 3, 4}) (B := {2, 4}) (by decide) (by decide)
  have d3 := dep_at h hdep 3 (A := {0, 3, 4}) (B := {0, 3}) (by decide) (by decide)
  have d4 := dep_at h hdep 4 (A := {0, 1, 4}) (B := {1, 4}) (by decide) (by decide)
  have n0 := hnorm 0
  have n1 := hnorm 1
  have n2 := hnorm 2
  have n3 := hnorm 3
  have n4 := hnorm 4
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- All 32 subsets of `Fin 5`. -/
def allSubsets : List (Finset (Fin 5)) := [∅, {0}, {1}, {2}, {3}, {4}, {0, 1}, {0, 2}, {0, 3}, {0, 4}, {1, 2}, {1, 3}, {1, 4}, {2, 3}, {2, 4}, {3, 4}, {0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 2, 3}, {0, 2, 4}, {0, 3, 4}, {1, 2, 3}, {1, 2, 4}, {1, 3, 4}, {2, 3, 4}, {0, 1, 2, 3}, {0, 1, 2, 4}, {0, 1, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4}, Finset.univ]

theorem mem_allSubsets : ∀ S : Finset (Fin 5), S ∈ allSubsets := by decide

/-- `hstar` is the unique maximiser of `h ↦ h [5]` on `P5`. -/
theorem eq_hstar_of_max (h : SetFn) (hP : h ∈ P5) (hmax : h Finset.univ = 5 / 2) :
    h = hstar := by
  obtain ⟨hpoly, hdep, hnorm⟩ := hP
  obtain ⟨p0_0, p0_1, p0_2, p0_3, p0_4, p0_01, p0_02, p0_14, p0_013, p0_0123, p0_0124, p0_012, p0_014⟩ := pin_0 h hpoly hdep hnorm hmax
  obtain ⟨p1_1, p1_2, p1_3, p1_4, p1_0, p1_12, p1_13, p1_02, p1_124, p1_1234, p1_0123, p1_123, p1_012⟩ := pin_1 h hpoly hdep hnorm hmax
  obtain ⟨p2_2, p2_3, p2_4, p2_0, p2_1, p2_23, p2_24, p2_13, p2_023, p2_0234, p2_1234, p2_234, p2_123⟩ := pin_2 h hpoly hdep hnorm hmax
  obtain ⟨p3_3, p3_4, p3_0, p3_1, p3_2, p3_34, p3_03, p3_24, p3_134, p3_0134, p3_0234, p3_034, p3_234⟩ := pin_3 h hpoly hdep hnorm hmax
  obtain ⟨p4_4, p4_0, p4_1, p4_2, p4_3, p4_04, p4_14, p4_03, p4_024, p4_0124, p4_0134, p4_014, p4_034⟩ := pin_4 h hpoly hdep hnorm hmax
  have he := hpoly.empty
  have v_e : hstar ∅ = 0 := hstar_polymatroid.empty
  have v_0 : hstar {0} = 1 := by
    unfold hstar
    rw [show (N ({0} : Finset (Fin 5))).card = 2 by decide]
    norm_num
  have v_1 : hstar {1} = 1 := by
    unfold hstar
    rw [show (N ({1} : Finset (Fin 5))).card = 2 by decide]
    norm_num
  have v_2 : hstar {2} = 1 := by
    unfold hstar
    rw [show (N ({2} : Finset (Fin 5))).card = 2 by decide]
    norm_num
  have v_3 : hstar {3} = 1 := by
    unfold hstar
    rw [show (N ({3} : Finset (Fin 5))).card = 2 by decide]
    norm_num
  have v_4 : hstar {4} = 1 := by
    unfold hstar
    rw [show (N ({4} : Finset (Fin 5))).card = 2 by decide]
    norm_num
  have v_01 : hstar {0, 1} = 3 / 2 := by
    unfold hstar
    rw [show (N ({0, 1} : Finset (Fin 5))).card = 3 by decide]
    norm_num
  have v_02 : hstar {0, 2} = 2 := by
    unfold hstar
    rw [show (N ({0, 2} : Finset (Fin 5))).card = 4 by decide]
    norm_num
  have v_03 : hstar {0, 3} = 2 := by
    unfold hstar
    rw [show (N ({0, 3} : Finset (Fin 5))).card = 4 by decide]
    norm_num
  have v_04 : hstar {0, 4} = 3 / 2 := by
    unfold hstar
    rw [show (N ({0, 4} : Finset (Fin 5))).card = 3 by decide]
    norm_num
  have v_12 : hstar {1, 2} = 3 / 2 := by
    unfold hstar
    rw [show (N ({1, 2} : Finset (Fin 5))).card = 3 by decide]
    norm_num
  have v_13 : hstar {1, 3} = 2 := by
    unfold hstar
    rw [show (N ({1, 3} : Finset (Fin 5))).card = 4 by decide]
    norm_num
  have v_14 : hstar {1, 4} = 2 := by
    unfold hstar
    rw [show (N ({1, 4} : Finset (Fin 5))).card = 4 by decide]
    norm_num
  have v_23 : hstar {2, 3} = 3 / 2 := by
    unfold hstar
    rw [show (N ({2, 3} : Finset (Fin 5))).card = 3 by decide]
    norm_num
  have v_24 : hstar {2, 4} = 2 := by
    unfold hstar
    rw [show (N ({2, 4} : Finset (Fin 5))).card = 4 by decide]
    norm_num
  have v_34 : hstar {3, 4} = 3 / 2 := by
    unfold hstar
    rw [show (N ({3, 4} : Finset (Fin 5))).card = 3 by decide]
    norm_num
  have v_012 : hstar {0, 1, 2} = 2 := by
    unfold hstar
    rw [show (N ({0, 1, 2} : Finset (Fin 5))).card = 4 by decide]
    norm_num
  have v_013 : hstar {0, 1, 3} = 5 / 2 := by
    unfold hstar
    rw [show (N ({0, 1, 3} : Finset (Fin 5))).card = 5 by decide]
    norm_num
  have v_014 : hstar {0, 1, 4} = 2 := by
    unfold hstar
    rw [show (N ({0, 1, 4} : Finset (Fin 5))).card = 4 by decide]
    norm_num
  have v_023 : hstar {0, 2, 3} = 5 / 2 := by
    unfold hstar
    rw [show (N ({0, 2, 3} : Finset (Fin 5))).card = 5 by decide]
    norm_num
  have v_024 : hstar {0, 2, 4} = 5 / 2 := by
    unfold hstar
    rw [show (N ({0, 2, 4} : Finset (Fin 5))).card = 5 by decide]
    norm_num
  have v_034 : hstar {0, 3, 4} = 2 := by
    unfold hstar
    rw [show (N ({0, 3, 4} : Finset (Fin 5))).card = 4 by decide]
    norm_num
  have v_123 : hstar {1, 2, 3} = 2 := by
    unfold hstar
    rw [show (N ({1, 2, 3} : Finset (Fin 5))).card = 4 by decide]
    norm_num
  have v_124 : hstar {1, 2, 4} = 5 / 2 := by
    unfold hstar
    rw [show (N ({1, 2, 4} : Finset (Fin 5))).card = 5 by decide]
    norm_num
  have v_134 : hstar {1, 3, 4} = 5 / 2 := by
    unfold hstar
    rw [show (N ({1, 3, 4} : Finset (Fin 5))).card = 5 by decide]
    norm_num
  have v_234 : hstar {2, 3, 4} = 2 := by
    unfold hstar
    rw [show (N ({2, 3, 4} : Finset (Fin 5))).card = 4 by decide]
    norm_num
  have v_0123 : hstar {0, 1, 2, 3} = 5 / 2 := by
    unfold hstar
    rw [show (N ({0, 1, 2, 3} : Finset (Fin 5))).card = 5 by decide]
    norm_num
  have v_0124 : hstar {0, 1, 2, 4} = 5 / 2 := by
    unfold hstar
    rw [show (N ({0, 1, 2, 4} : Finset (Fin 5))).card = 5 by decide]
    norm_num
  have v_0134 : hstar {0, 1, 3, 4} = 5 / 2 := by
    unfold hstar
    rw [show (N ({0, 1, 3, 4} : Finset (Fin 5))).card = 5 by decide]
    norm_num
  have v_0234 : hstar {0, 2, 3, 4} = 5 / 2 := by
    unfold hstar
    rw [show (N ({0, 2, 3, 4} : Finset (Fin 5))).card = 5 by decide]
    norm_num
  have v_1234 : hstar {1, 2, 3, 4} = 5 / 2 := by
    unfold hstar
    rw [show (N ({1, 2, 3, 4} : Finset (Fin 5))).card = 5 by decide]
    norm_num
  have v_u : hstar Finset.univ = 5 / 2 := by
    unfold hstar
    rw [show (N (Finset.univ : Finset (Fin 5))).card = 5 by decide]
    norm_num
  funext S
  have hS := mem_allSubsets S
  simp only [allSubsets, List.mem_cons, List.mem_nil_iff, or_false] at hS
  rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [v_e]; exact he
  · rw [v_0]; exact p0_0
  · rw [v_1]; exact p0_1
  · rw [v_2]; exact p0_2
  · rw [v_3]; exact p0_3
  · rw [v_4]; exact p0_4
  · rw [v_01]; exact p0_01
  · rw [v_02]; exact p0_02
  · rw [v_03]; exact p3_03
  · rw [v_04]; exact p4_04
  · rw [v_12]; exact p1_12
  · rw [v_13]; exact p1_13
  · rw [v_14]; exact p0_14
  · rw [v_23]; exact p2_23
  · rw [v_24]; exact p2_24
  · rw [v_34]; exact p3_34
  · rw [v_012]; exact p0_012
  · rw [v_013]; exact p0_013
  · rw [v_014]; exact p0_014
  · rw [v_023]; exact p2_023
  · rw [v_024]; exact p4_024
  · rw [v_034]; exact p3_034
  · rw [v_123]; exact p1_123
  · rw [v_124]; exact p1_124
  · rw [v_134]; exact p3_134
  · rw [v_234]; exact p2_234
  · rw [v_0123]; exact p0_0123
  · rw [v_0124]; exact p0_0124
  · rw [v_0134]; exact p3_0134
  · rw [v_0234]; exact p2_0234
  · rw [v_1234]; exact p1_1234
  · rw [v_u]; exact hmax

/-! ### Extreme point and non-integrality -/

theorem eq_of_avg {a b u v c : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hz : a * u + b * v = c) (hu : u ≤ c) (hv : v ≤ c) : u = c ∧ v = c := by
  have h1 : a * (c - u) + b * (c - v) = 0 := by linear_combination -hz + c * hab
  have h2 : 0 ≤ a * (c - u) := mul_nonneg ha.le (by linarith)
  have h3 : 0 ≤ b * (c - v) := mul_nonneg hb.le (by linarith)
  have h4 : a * (c - u) = 0 := by linarith
  have h5 : b * (c - v) = 0 := by linarith
  rcases mul_eq_zero.1 h4 with h | h
  · exact absurd h ha.ne'
  rcases mul_eq_zero.1 h5 with h' | h'
  · exact absurd h' hb.ne'
  constructor <;> linarith

/-- `hstar` is an extreme point (vertex) of the polytope `P5`: it is the unique
maximiser of the linear functional `h ↦ h [5]`. -/
theorem hstar_extreme : hstar ∈ Set.extremePoints ℝ P5 := by
  rw [mem_extremePoints]
  refine ⟨hstar_mem, ?_⟩
  intro x₁ hx₁ x₂ hx₂ hseg
  obtain ⟨a, b, ha, hb, hab, hz⟩ := hseg
  have hz' : a * x₁ Finset.univ + b * x₂ Finset.univ = 5 / 2 := by
    have := congrFun hz Finset.univ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [this, hstar_univ]
  obtain ⟨e1, e2⟩ := eq_of_avg ha hb hab hz' (le_five_halves x₁ hx₁) (le_five_halves x₂ hx₂)
  exact ⟨eq_hstar_of_max x₁ hx₁ e1, eq_hstar_of_max x₂ hx₂ e2⟩

/-- The vertex has non-integer coordinates. -/
theorem hstar_pair_not_integer : ∀ z : ℤ, (z : ℝ) ≠ hstar {0, 1} := by
  intro z hz
  rw [hstar_pair] at hz
  have h2 : (2 * z : ℤ) = 3 := by
    have : (2 * (z : ℝ)) = 3 := by linarith
    exact_mod_cast this
  omega

/-- Summary statement: the maximum of `h [5]` over `P5` is `5/2`, attained
exactly at `hstar`, an extreme point with a non-integer coordinate. -/
theorem five_cycle_vertex :
    (∀ h ∈ P5, h Finset.univ ≤ 5 / 2) ∧ hstar ∈ P5 ∧ hstar Finset.univ = 5 / 2 ∧
    (∀ h ∈ P5, h Finset.univ = 5 / 2 → h = hstar) ∧
    hstar ∈ Set.extremePoints ℝ P5 ∧ (∀ z : ℤ, (z : ℝ) ≠ hstar {0, 1}) :=
  ⟨le_five_halves, hstar_mem, hstar_univ, eq_hstar_of_max, hstar_extreme,
    hstar_pair_not_integer⟩

end TermCoding.Examples.C5Entropy
