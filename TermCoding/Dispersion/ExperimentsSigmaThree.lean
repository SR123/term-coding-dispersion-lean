import TermCoding.Dispersion.Experiments
import Mathlib.Algebra.BigOperators.Fin

/-!
# Kernel check: `σ` has no 3-element witness (V6, Section 7.1)

The remaining small case of the `k = 2` experiments: no binary operation on
a three-element set makes `σ(x,y) = (f(x,y), f(f(x,x), f(y,y)))` bijective.

The `3^9 = 19683` operation tables are encoded as base-`3` digit strings of
natural numbers, and the collision search is a pure-arithmetic statement
decided by the Lean kernel (`sigma_all_tables_collide`; no native
evaluation).  The bridge lemmas (`tblDigit_encodeTbl`, `sigmaOutN_encodeTbl`)
identify the arithmetic outputs with the actual `σ` term map of an arbitrary
table, giving `sigma_no_witness_three` and, with the two- and four-element
results of `Experiments.lean`, the fully checked statement
`sigma_bijectivity_spectrum_low`: the least alphabet size admitting a
`σ`-witness is `4`.
-/

namespace TermCoding

namespace Dispersion

/-- Base-`3` digit `3x + y` of the encoded table `e`. -/
def tblDigit (e x y : ℕ) : ℕ := e / 3 ^ (3 * x + y) % 3

/-- The `σ`-output of table `e` at `(x, y)`, packed as a number `< 9`. -/
def sigmaOutN (e x y : ℕ) : ℕ :=
  tblDigit e x y * 3 + tblDigit e (tblDigit e x x) (tblDigit e y y)

/-- Does input `u` collide with some input `v < V`? (Instance-free Bool
recursion, kernel-reducible.) -/
def collideWith (e u : ℕ) : ℕ → Bool
  | 0 => false
  | v + 1 => (sigmaOutN e (u / 3) (u % 3) == sigmaOutN e (v / 3) (v % 3)) || collideWith e u v

/-- Does some pair `v < u < U` collide? -/
def collideBelow (e : ℕ) : ℕ → Bool
  | 0 => false
  | u + 1 => collideWith e u u || collideBelow e u

/-- Collision search over the `36` unordered input pairs. -/
def sigmaCollides (e : ℕ) : Bool := collideBelow e 9

/-- Do all tables `e < E` collide? -/
def allCollide : ℕ → Bool
  | 0 => true
  | e + 1 => sigmaCollides e && allCollide e

/-- Every one of the `19683` tables has a collision (kernel reduction of a
single Bool recursion; no native evaluation). -/
theorem sigma_all_tables_collide : allCollide 19683 = true := by decide +kernel

theorem collideWith_spec (e u : ℕ) :
    ∀ V, collideWith e u V = true →
      ∃ v, v < V ∧ sigmaOutN e (u / 3) (u % 3) = sigmaOutN e (v / 3) (v % 3) := by
  intro V
  induction V with
  | zero => intro h; exact absurd h (by simp [collideWith])
  | succ V ih =>
      intro h
      rw [collideWith, Bool.or_eq_true] at h
      rcases h with h | h
      · exact ⟨V, by omega, by simpa using h⟩
      · obtain ⟨v, hv, heq⟩ := ih h
        exact ⟨v, by omega, heq⟩

theorem collideBelow_spec (e : ℕ) :
    ∀ U, collideBelow e U = true →
      ∃ u, u < U ∧ ∃ v, v < u ∧
        sigmaOutN e (u / 3) (u % 3) = sigmaOutN e (v / 3) (v % 3) := by
  intro U
  induction U with
  | zero => intro h; exact absurd h (by simp [collideBelow])
  | succ U ih =>
      intro h
      rw [collideBelow, Bool.or_eq_true] at h
      rcases h with h | h
      · obtain ⟨v, hv, heq⟩ := collideWith_spec e U U h
        exact ⟨U, by omega, v, hv, heq⟩
      · obtain ⟨u, hu, hrest⟩ := ih h
        exact ⟨u, by omega, hrest⟩

theorem allCollide_spec : ∀ E, allCollide E = true → ∀ e, e < E → sigmaCollides e = true := by
  intro E
  induction E with
  | zero => intro _ e he; omega
  | succ E ih =>
      intro h e he
      rw [allCollide, Bool.and_eq_true] at h
      rcases Nat.lt_succ_iff_lt_or_eq.mp he with h' | rfl
      · exact ih h.2 e h'
      · exact h.1

/-- The base-`3` encoding of an operation table. -/
def encodeTbl (g : Fin 3 → Fin 3 → Fin 3) : ℕ :=
  ∑ x : Fin 3, ∑ y : Fin 3, (g x y).val * 3 ^ (3 * x.val + y.val)

theorem encodeTbl_lt (g : Fin 3 → Fin 3 → Fin 3) : encodeTbl g < 19683 := by
  have h00 := (g 0 0).isLt
  have h01 := (g 0 1).isLt
  have h02 := (g 0 2).isLt
  have h10 := (g 1 0).isLt
  have h11 := (g 1 1).isLt
  have h12 := (g 1 2).isLt
  have h20 := (g 2 0).isLt
  have h21 := (g 2 1).isLt
  have h22 := (g 2 2).isLt
  unfold encodeTbl
  simp [Fin.sum_univ_three]
  omega

/-- Digit extraction recovers the table. -/
theorem tblDigit_encodeTbl (g : Fin 3 → Fin 3 → Fin 3) :
    ∀ x y : Fin 3, tblDigit (encodeTbl g) x.val y.val = (g x y).val := by
  have h00 := (g 0 0).isLt
  have h01 := (g 0 1).isLt
  have h02 := (g 0 2).isLt
  have h10 := (g 1 0).isLt
  have h11 := (g 1 1).isLt
  have h12 := (g 1 2).isLt
  have h20 := (g 2 0).isLt
  have h21 := (g 2 1).isLt
  have h22 := (g 2 2).isLt
  intro x y
  fin_cases x <;> fin_cases y <;>
    (simp [tblDigit, encodeTbl, Fin.sum_univ_three]
     omega)

/-- The packed arithmetic output is the actual `σ` output of the table. -/
theorem sigmaOutN_encodeTbl (g : Fin 3 → Fin 3 → Fin 3) (x y : Fin 3) :
    sigmaOutN (encodeTbl g) x.val y.val =
      (g x y).val * 3 + (g (g x x) (g y y)).val := by
  unfold sigmaOutN
  rw [tblDigit_encodeTbl g x y, tblDigit_encodeTbl g x x, tblDigit_encodeTbl g y y,
    tblDigit_encodeTbl g (g x x) (g y y)]

/-- The `σ` term map, in coordinates. -/
theorem termMap_sigmaPair (g : Fin 3 → Fin 3 → Fin 3) (x y : Fin 3) :
    termMap sigmaPair (diamondInterp g) ![x, y] =
      ![g x y, g (g x x) (g y y)] := by
  funext i
  fin_cases i <;> rfl

/-- No binary operation on a three-element set makes `σ` bijective. -/
theorem sigma_no_witness_three :
    ¬ ∃ g : Fin 3 → Fin 3 → Fin 3,
      Function.Bijective (termMap sigmaPair (diamondInterp g)) := by
  rintro ⟨g, hbij⟩
  set e := encodeTbl g with he
  have helt : e < 19683 := encodeTbl_lt g
  have hcoll : sigmaCollides e = true :=
    allCollide_spec 19683 sigma_all_tables_collide e helt
  have hex := collideBelow_spec e 9 hcoll
  obtain ⟨u, hu9, v, hvu, heq⟩ := hex
  -- decode the two colliding inputs
  let xu : Fin 3 := ⟨u / 3, by omega⟩
  let yu : Fin 3 := ⟨u % 3, by omega⟩
  let xv : Fin 3 := ⟨v / 3, by omega⟩
  let yv : Fin 3 := ⟨v % 3, by omega⟩
  have hequ : sigmaOutN e xu.val yu.val = sigmaOutN e xv.val yv.val := heq
  rw [he, sigmaOutN_encodeTbl g xu yu, sigmaOutN_encodeTbl g xv yv] at hequ
  have hb1 := (g xu yu).isLt
  have hb2 := (g (g xu xu) (g yu yu)).isLt
  have hb3 := (g xv yv).isLt
  have hb4 := (g (g xv xv) (g yv yv)).isLt
  have hfst : (g xu yu).val = (g xv yv).val := by omega
  have hsnd : (g (g xu xu) (g yu yu)).val = (g (g xv xv) (g yv yv)).val := by omega
  -- the term maps collide at two distinct inputs
  have hout : termMap sigmaPair (diamondInterp g) ![xu, yu] =
      termMap sigmaPair (diamondInterp g) ![xv, yv] := by
    rw [termMap_sigmaPair, termMap_sigmaPair]
    have h1 : g xu yu = g xv yv := Fin.ext hfst
    have h2 : g (g xu xu) (g yu yu) = g (g xv xv) (g yv yv) := Fin.ext hsnd
    rw [h1, h2]
  have hin := hbij.1 hout
  have hx := congrFun hin 0
  have hy := congrFun hin 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
  have hxv : u / 3 = v / 3 := congrArg Fin.val hx
  have hyv : u % 3 = v % 3 := congrArg Fin.val hy
  omega

/-- The complete kernel-checked low-size picture for `σ`: no witness on `2`
or `3` elements, and an explicit witness on `4`; hence `4` is the least
alphabet size at which `σ` is a `BIJ_2`-witnessed instance. -/
theorem sigma_bijectivity_spectrum_low :
    (¬ ∃ g : Fin 2 → Fin 2 → Fin 2,
        Function.Bijective (termMap sigmaPair (diamondInterp g))) ∧
    (¬ ∃ g : Fin 3 → Fin 3 → Fin 3,
        Function.Bijective (termMap sigmaPair (diamondInterp g))) ∧
    ∃ g : Fin 4 → Fin 4 → Fin 4,
        Function.Bijective (termMap sigmaPair (diamondInterp g)) :=
  ⟨sigma_no_witness_two, sigma_no_witness_three, sigmaTable, sigma_witness_four⟩

end Dispersion

end TermCoding
