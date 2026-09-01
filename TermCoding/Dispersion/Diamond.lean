import TermCoding.Dispersion.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The single-function diamond gadget (V6, `ex:diamond`, `lem:diamond-not-bij`)

The instance `t(x,y,z,w) = (f(x,y), f(x,z), f(y,w), f(z,w))` with one shared
binary symbol `f`.

* `diamond_not_injective` -- `lem:diamond-not-bij`: for every finite alphabet
  with at least two elements and every interpretation of `f`, the induced map
  `A^4 → A^4` is not injective (hence, by finiteness, not surjective).  The
  proof is the manuscript's pigeonhole argument on the slice `y = z`, using
  `2 ≤ |A|` exactly where `|A|^3 > |A|^2` is needed.
* `diamond_not_perfect` -- the diamond is never perfectly dispersive.
* `diversifiedDiamond_bijective` -- the contrast remark: with four independent
  symbols the map can be made bijective on every alphabet.
* `pow_le_dispN_diamond` -- an explicit *shared-symbol* interpretation on the
  tagged alphabet `Fin 4 × Fin m` with image of size at least `m^4`.  This is
  the "dynamic routing" mechanism of the 2019 source specialised to the
  diamond; it is what makes `D(t) = 4` provable without the external theorem
  (see `TermCoding.Dispersion.Exponent`).
-/

namespace TermCoding

namespace Dispersion

/-- The signature with exactly one binary symbol. -/
def diamondSignature : Signature where
  Symbol := Unit
  arity := fun _ => 2

instance : Fintype diamondSignature.Symbol := inferInstanceAs (Fintype Unit)

/-- `f(a, b)` as a term over the diamond signature. -/
def fapp {V : Type} (a b : Term diamondSignature V) : Term diamondSignature V :=
  .app () ![a, b]

/-- `eq:diamond-terms`: inputs `x = 0, y = 1, z = 2, w = 3`. -/
def diamond : Instance diamondSignature 4 4 :=
  ![fapp (.var 0) (.var 1), fapp (.var 0) (.var 2),
    fapp (.var 1) (.var 3), fapp (.var 2) (.var 3)]

/-- An interpretation of the diamond signature is one binary operation. -/
def diamondInterp {A : Type*} (g : A → A → A) : Interpretation diamondSignature A :=
  fun _ (input : Fin 2 → A) => g (input 0) (input 1)

theorem fin2_eta {A : Type*} (input : Fin 2 → A) : ![input 0, input 1] = input := by
  funext p
  fin_cases p <;> rfl

/-- Every interpretation of the diamond signature is of the form
`diamondInterp g`. -/
theorem diamondInterp_surjective {A : Type*} (I : Interpretation diamondSignature A) :
    I = diamondInterp (fun a b => I () ![a, b]) := by
  funext s input
  cases s
  exact congrArg (I ()) (fin2_eta input).symm

theorem termMap_diamond {A : Type*} (g : A → A → A) (x : Fin 4 → A) :
    termMap diamond (diamondInterp g) x =
      ![g (x 0) (x 1), g (x 0) (x 2), g (x 1) (x 3), g (x 2) (x 3)] := by
  funext i
  fin_cases i <;> rfl

/-- `lem:diamond-not-bij`: the diamond map is never injective on an alphabet
with at least two elements. -/
theorem diamond_not_injective {A : Type*} [Fintype A] (hA : 2 ≤ Fintype.card A)
    (I : Interpretation diamondSignature A) :
    ¬ Function.Injective (termMap diamond I) := by
  intro hinj
  rw [diamondInterp_surjective I] at hinj
  set g := fun a b => I () ![a, b]
  -- the slice `y = z`
  let φ : A × A × A → (Fin 4 → A) := fun p => ![p.1, p.2.1, p.2.1, p.2.2]
  have hφ : Function.Injective φ := by
    intro p q h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h3 := congrFun h 3
    simp [φ] at h0 h1 h3
    exact Prod.ext h0 (Prod.ext h1 h3)
  -- on the slice the output has the form `(a, a, b, b)`
  let ρ : A × A × A → A × A := fun p => (g p.1 p.2.1, g p.2.1 p.2.2)
  let ψ : A × A → (Fin 4 → A) := fun q => ![q.1, q.1, q.2, q.2]
  have hfactor : termMap diamond (diamondInterp g) ∘ φ = ψ ∘ ρ := by
    funext p
    simp only [Function.comp, φ, ψ, ρ, termMap_diamond]
    rfl
  have hρ : Function.Injective ρ := by
    intro p q h
    apply hφ
    apply hinj
    change (termMap diamond (diamondInterp g) ∘ φ) p =
      (termMap diamond (diamondInterp g) ∘ φ) q
    rw [hfactor]
    simp only [Function.comp]
    rw [h]
  have hcard := Fintype.card_le_of_injective ρ hρ
  simp only [Fintype.card_prod] at hcard
  have h3 : Fintype.card A * (Fintype.card A * Fintype.card A) =
      Fintype.card A ^ 3 := by ring
  have h2 : Fintype.card A * Fintype.card A = Fintype.card A ^ 2 := by ring
  rw [h3, h2] at hcard
  have : Fintype.card A ^ 2 < Fintype.card A ^ 3 :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  omega

/-- On a finite alphabet with at least two elements the diamond map is never
surjective (`lem:diamond-not-bij`, "hence not bijective/surjective"). -/
theorem diamond_not_surjective {A : Type*} [Fintype A] (hA : 2 ≤ Fintype.card A)
    (I : Interpretation diamondSignature A) :
    ¬ Function.Surjective (termMap diamond I) := by
  intro h
  exact diamond_not_injective hA I ((injective_iff_surjective_square diamond I).2 h)

/-- The diamond never reaches `n^4`; `Disp_n(t) < n^4` for every `n ≥ 2`. -/
theorem dispN_diamond_lt (n : Nat) (hn : 2 ≤ n) : dispN diamond n < n ^ 4 := by
  refine lt_of_le_of_ne (dispN_le_pow diamond n) ?_
  intro h
  obtain ⟨I, hI⟩ := (dispN_eq_pow_iff diamond (by omega)).1 h
  exact diamond_not_surjective (by simpa using hn) I hI

/-- The diamond gadget is a no-instance of `Perfect-Disp`. -/
theorem diamond_not_perfect : ¬ PerfectDisp diamond := by
  rintro ⟨n, hn, h⟩
  exact absurd h (ne_of_lt (dispN_diamond_lt n hn))

/-! ### Contrast: diversification removes the obstruction -/

/-- Four independent binary symbols `f_1, …, f_4`. -/
def diversifiedDiamondSignature : Signature where
  Symbol := Fin 4
  arity := fun _ => 2

/-- `(f_1(x,y), f_2(x,z), f_3(y,w), f_4(z,w))`. -/
def diversifiedDiamond : Instance diversifiedDiamondSignature 4 4 :=
  ![.app (0 : Fin 4) ![.var 0, .var 1], .app (1 : Fin 4) ![.var 0, .var 2],
    .app (2 : Fin 4) ![.var 1, .var 3], .app (3 : Fin 4) ![.var 2, .var 3]]

/-- The interpretation `f_1(x,y) = x`, `f_2(x,z) = z`, `f_3(y,w) = y`,
`f_4(z,w) = w`. -/
def diversifiedDiamondInterp (A : Type*) : Interpretation diversifiedDiamondSignature A :=
  fun (s : Fin 4) (input : Fin 2 → A) =>
    if s.val = 1 ∨ s.val = 3 then input 1 else input 0

/-- With independent symbols the diamond map becomes the coordinate
permutation `(x,y,z,w) ↦ (x,z,y,w)`, which is bijective on every alphabet. -/
theorem diversifiedDiamond_bijective (A : Type*) :
    Function.Bijective (termMap diversifiedDiamond (diversifiedDiamondInterp A)) := by
  have hmap : termMap diversifiedDiamond (diversifiedDiamondInterp A) =
      fun x => ![x 0, x 2, x 1, x 3] := by
    funext x i
    fin_cases i <;> rfl
  rw [hmap]
  constructor
  · intro x y h
    funext i
    fin_cases i
    · exact congrFun h 0
    · exact congrFun h 2
    · exact congrFun h 1
    · exact congrFun h 3
  · intro y
    refine ⟨![y 0, y 2, y 1, y 3], ?_⟩
    funext i
    fin_cases i <;> rfl

/-! ### A shared-symbol interpretation with a large image -/

/-- The tagged alphabet `Fin 4 × Fin m`: a value `(i, b)` is "block value `b`
belonging to input variable `i`".  The single operation `g` reads the tags
of its two arguments to decide which block to forward: it forwards the
*first* argument on the tag pairs `(x,y)` and `(y,w)` and the *second*
argument on `(x,z)` and `(z,w)`.  This is the 2019 "dynamic routing" idea
specialised to the diamond. -/
def diamondRouting (m : Nat) : Fin 4 × Fin m → Fin 4 × Fin m → Fin 4 × Fin m :=
  fun a b =>
    if (a.1.val = 0 ∧ b.1.val = 1) ∨ (a.1.val = 1 ∧ b.1.val = 3) then (0, a.2)
    else (0, b.2)

/-- The input assignment carrying block values `b` with the canonical tags. -/
def taggedInput (m : Nat) (b : Fin 4 → Fin m) : Fin 4 → Fin 4 × Fin m :=
  fun i => (i, b i)

theorem termMap_diamond_routing (m : Nat) (b : Fin 4 → Fin m) :
    termMap diamond (diamondInterp (diamondRouting m)) (taggedInput m b) =
      ![(0, b 0), (0, b 2), (0, b 1), (0, b 3)] := by
  rw [termMap_diamond]
  funext i
  fin_cases i <;> simp [diamondRouting, taggedInput]

/-- The routing interpretation has image of size at least `m^4` on the
alphabet `Fin 4 × Fin m`. -/
theorem pow_le_imageCard_diamondRouting (m : Nat) :
    m ^ 4 ≤ imageCard diamond (diamondInterp (diamondRouting m)) := by
  unfold imageCard
  let φ : (Fin 4 → Fin m) → Set.range (termMap diamond (diamondInterp (diamondRouting m))) :=
    fun b => ⟨termMap diamond (diamondInterp (diamondRouting m)) (taggedInput m b),
      ⟨taggedInput m b, rfl⟩⟩
  have hφ : Function.Injective φ := by
    intro b c h
    have h' := congrArg Subtype.val h
    simp only [φ] at h'
    rw [termMap_diamond_routing, termMap_diamond_routing] at h'
    funext i
    fin_cases i
    · exact congrArg Prod.snd (congrFun h' 0)
    · exact congrArg Prod.snd (congrFun h' 2)
    · exact congrArg Prod.snd (congrFun h' 1)
    · exact congrArg Prod.snd (congrFun h' 3)
  have := Nat.card_le_card_of_injective φ hφ
  simpa [Nat.card_eq_fintype_card, Fintype.card_fun] using this

/-- `m^4 ≤ Disp_{4m}(diamond)`: the shared-symbol diamond has dispersion of
order `n^4` along the alphabet sizes `n = 4m`. -/
theorem pow_le_dispN_diamond (m : Nat) : m ^ 4 ≤ dispN diamond (4 * m) := by
  have h1 := pow_le_imageCard_diamondRouting m
  have h2 := imageCard_le_disp (A := Fin 4 × Fin m) diamond
    (diamondInterp (diamondRouting m))
  have h3 := disp_eq_dispN (A := Fin 4 × Fin m) diamond
  simp only [Fintype.card_prod, Fintype.card_fin] at h3
  omega

/-- For every `n ≥ 4`, `⌊n/4⌋^4 ≤ Disp_n(diamond)`; in particular
`Disp_n(diamond) ≥ n^4 / 8^4` for `n ≥ 8`. -/
theorem div_pow_le_dispN_diamond (n : Nat) (hn : 4 ≤ n) :
    (n / 4) ^ 4 ≤ dispN diamond n := by
  have h1 := pow_le_dispN_diamond (n / 4)
  have h2 : dispN diamond (4 * (n / 4)) ≤ dispN diamond n :=
    dispN_mono diamond (by omega) (Nat.mul_div_le n 4)
  omega

end Dispersion

end TermCoding
