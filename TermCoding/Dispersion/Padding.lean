import TermCoding.Dispersion.Basic
import Mathlib.Data.Fintype.Pi

/-!
# Padding lemmas (V6, Section 6.3)

* `padMap_surjective_iff` -- `lem:padding-outputs`: for `k ≥ r ≥ k₀` and
  `p : A^{k₀} → A^{k₀}`, the map
  `F(a_1,…,a_k) = (p(a_1,…,a_{k₀}), a_{k₀+1}, …, a_r)` is surjective iff `p`
  is.  The manuscript's proof chooses "the remaining inputs arbitrarily if
  `k > r`"; this needs a default element, so the lemma is stated for a
  `Nonempty` alphabet.  `padMap_not_surjective_empty` records the degenerate
  failure without that hypothesis (`A = ∅`, `k₀ = r = 0`, `k = 1`).
* `restrictMap_surjective_iff` -- `lem:unused-inputs`: unused trailing inputs
  do not affect surjectivity (again with `Nonempty A` when `k > r`).
-/

namespace TermCoding

namespace Dispersion

universe uAlpha

variable {A : Type uAlpha}

/-- The first `k₀` coordinates of a `k`-tuple. -/
def headCoords {k₀ k : Nat} (h : k₀ ≤ k) (a : Fin k → A) : Fin k₀ → A :=
  fun j => a (Fin.castLE h j)

/-- `F(a_1,…,a_k) := (p(a_1,…,a_{k₀}), a_{k₀+1}, …, a_r)`. -/
def padMap {k₀ r k : Nat} (p : (Fin k₀ → A) → (Fin k₀ → A))
    (hk₀r : k₀ ≤ r) (hrk : r ≤ k) : (Fin k → A) → (Fin r → A) :=
  fun a i =>
    if h : i.val < k₀ then p (headCoords (hk₀r.trans hrk) a) ⟨i.val, h⟩
    else a (Fin.castLE hrk i)

/-- `lem:padding-outputs` (with the nonemptiness needed to choose the unused
inputs when `k > r`). -/
theorem padMap_surjective_iff [Nonempty A] {k₀ r k : Nat}
    (p : (Fin k₀ → A) → (Fin k₀ → A)) (hk₀r : k₀ ≤ r) (hrk : r ≤ k) :
    Function.Surjective (padMap p hk₀r hrk) ↔ Function.Surjective p := by
  constructor
  · intro hF b
    -- extend `b` by arbitrary trailing coordinates
    let c : A := Classical.choice inferInstance
    let b' : Fin r → A := fun i => if h : i.val < k₀ then b ⟨i.val, h⟩ else c
    obtain ⟨a, ha⟩ := hF b'
    refine ⟨headCoords (hk₀r.trans hrk) a, ?_⟩
    funext j
    have hj := congrFun ha (Fin.castLE hk₀r j)
    simp only [padMap, b', Fin.coe_castLE, Fin.is_lt, dite_true] at hj
    exact hj
  · intro hp b
    let c : A := Classical.choice inferInstance
    obtain ⟨a₀, ha₀⟩ := hp (headCoords hk₀r b)
    -- `a` agrees with `a₀` on the first `k₀` coordinates, with `b` on the
    -- next `r - k₀`, and is arbitrary on the last `k - r`
    let a : Fin k → A := fun i =>
      if h₀ : i.val < k₀ then a₀ ⟨i.val, h₀⟩
      else if h₁ : i.val < r then b ⟨i.val, h₁⟩ else c
    refine ⟨a, ?_⟩
    have hhead : headCoords (hk₀r.trans hrk) a = a₀ := by
      funext j
      simp [headCoords, a, Fin.is_lt]
    funext i
    simp only [padMap, hhead]
    by_cases h : i.val < k₀
    · rw [dif_pos h]
      have := congrFun ha₀ ⟨i.val, h⟩
      simp only [headCoords] at this
      rw [this]
      congr 1
    · rw [dif_neg h]
      simp [a, h, Fin.is_lt]

/-- The degenerate case: without a default element the backward direction
of `lem:padding-outputs` fails when `k > r`.  Here `A = Empty`, `k₀ = r = 0`,
`k = 1`, and `p = id` is surjective while `F` is not. -/
theorem padMap_not_surjective_empty :
    ¬ Function.Surjective
      (padMap (A := Empty) (k₀ := 0) (r := 0) (k := 1) id le_rfl (by omega)) := by
  intro h
  obtain ⟨a, _⟩ := h (fun i => Fin.elim0 i)
  exact (a 0).elim

/-- `F(a_1,…,a_k) := f(a_1,…,a_r)`, the map that ignores its trailing inputs. -/
def restrictMap {r k : Nat} (f : (Fin r → A) → (Fin r → A)) (hrk : r ≤ k) :
    (Fin k → A) → (Fin r → A) :=
  fun a => f (headCoords hrk a)

/-- `lem:unused-inputs`: the images of `F` and `f` coincide, so `F` is
surjective iff `f` is (`Nonempty A` supplies the unused inputs). -/
theorem restrictMap_surjective_iff [Nonempty A] {r k : Nat}
    (f : (Fin r → A) → (Fin r → A)) (hrk : r ≤ k) :
    Function.Surjective (restrictMap f hrk) ↔ Function.Surjective f := by
  constructor
  · intro hF b
    obtain ⟨a, ha⟩ := hF b
    exact ⟨headCoords hrk a, ha⟩
  · intro hf b
    obtain ⟨a₀, ha₀⟩ := hf b
    let c : A := Classical.choice inferInstance
    let a : Fin k → A := fun i => if h : i.val < r then a₀ ⟨i.val, h⟩ else c
    refine ⟨a, ?_⟩
    have hhead : headCoords hrk a = a₀ := by
      funext j
      simp [headCoords, a, Fin.is_lt]
    simp only [restrictMap, hhead, ha₀]

/-- The ranges of `F` and `f` coincide exactly (the manuscript's one-line
proof of `lem:unused-inputs`), given a default element. -/
theorem range_restrictMap [Nonempty A] {r k : Nat}
    (f : (Fin r → A) → (Fin r → A)) (hrk : r ≤ k) :
    Set.range (restrictMap f hrk) = Set.range f := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨headCoords hrk a, rfl⟩
  · rintro ⟨a₀, rfl⟩
    let c : A := Classical.choice inferInstance
    let a : Fin k → A := fun i => if h : i.val < r then a₀ ⟨i.val, h⟩ else c
    refine ⟨a, ?_⟩
    have hhead : headCoords hrk a = a₀ := by
      funext j
      simp [headCoords, a, Fin.is_lt]
    simp only [restrictMap, hhead]

end Dispersion

end TermCoding
