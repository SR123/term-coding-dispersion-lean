import TermCoding.Examples.C5EntropyPolytope
import TermCoding.Examples.C5
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.FinCases

/-!
# The five-cycle vertex is an entropy vector

Second half of Proposition 7.1 (journal version of Paper 1).  With
`n = m²` and `U = (U_0, …, U_4)` uniform on `[m]^5`, the configurations
`X_i = (U_i, U_{i+1})` are exactly the winning configurations of the
square-alphabet strategy `pairStrategy` of `TermCoding.Examples.C5`
(`wins_iff_exists_cycle`), there are exactly `m^5` of them
(`card_winners`), and for every `S ⊆ [5]` the Shannon entropy of the
coordinate projection `X_S`, under the uniform distribution on the winning
set, equals `|N S| · log m`, i.e. `hstar S · log n`
(`uniformEntropy_projS`, `hstar_eq_normalisedEntropy`).

Entropy is defined explicitly (`uniformEntropy`): the Shannon entropy, with
natural logarithm, of the push-forward of the uniform distribution on a
finite nonempty type `Ω` along a map `X : Ω → V`.  No entropy facts are
assumed.

Author: Claude (Fable 5), 27 August 2026.
-/

namespace TermCoding.Examples.C5Entropy

open Finset

/-! ### Shannon entropy of the push-forward of a uniform distribution -/

section Entropy

variable {Ω : Type*} [Fintype Ω] {V : Type*} [DecidableEq V]

/-- Probability that `X = v` when `Ω` carries the uniform distribution. -/
noncomputable def uniformProb (X : Ω → V) (v : V) : ℝ :=
  ((Finset.univ.filter (fun ω => X ω = v)).card : ℝ) / Fintype.card Ω

/-- Shannon entropy (natural logarithm) of `X` under the uniform distribution
on `Ω`: `-∑_v p(v) log p(v)` over the values `v` actually taken. -/
noncomputable def uniformEntropy (X : Ω → V) : ℝ :=
  ∑ v ∈ Finset.univ.image X, -(uniformProb X v * Real.log (uniformProb X v))

theorem card_eq_image_mul_of_const_fibre (X : Ω → V) (k : ℕ)
    (hfib : ∀ v ∈ Finset.univ.image X,
      (Finset.univ.filter (fun ω => X ω = v)).card = k) :
    Fintype.card Ω = (Finset.univ.image X).card * k := by
  rw [← Finset.card_univ]
  rw [Finset.card_eq_sum_card_fiberwise (f := X) (s := Finset.univ)
    (t := Finset.univ.image X) (fun x _ => Finset.mem_image_of_mem X (Finset.mem_univ x))]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]

/-- If every value taken by `X` has the same number `k > 0` of preimages, the
entropy is the logarithm of the number of values. -/
theorem uniformEntropy_of_const_fibre [Nonempty Ω] (X : Ω → V) (k : ℕ) (hk : 0 < k)
    (hfib : ∀ v ∈ Finset.univ.image X,
      (Finset.univ.filter (fun ω => X ω = v)).card = k) :
    uniformEntropy X = Real.log ((Finset.univ.image X).card : ℝ) := by
  have hcard : Fintype.card Ω = (Finset.univ.image X).card * k :=
    card_eq_image_mul_of_const_fibre X k hfib
  have hMpos : 0 < (Finset.univ.image X).card :=
    Finset.card_pos.2 (Finset.univ_nonempty.image X)
  have hMr : (0 : ℝ) < ((Finset.univ.image X).card : ℝ) := by exact_mod_cast hMpos
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hprob : ∀ v ∈ Finset.univ.image X,
      uniformProb X v = 1 / ((Finset.univ.image X).card : ℝ) := by
    intro v hv
    unfold uniformProb
    rw [hfib v hv, hcard, Nat.cast_mul]
    field_simp
  have hsum : ∑ v ∈ Finset.univ.image X, -(uniformProb X v * Real.log (uniformProb X v)) =
      ∑ _v ∈ Finset.univ.image X,
        -(1 / ((Finset.univ.image X).card : ℝ) *
          Real.log (1 / ((Finset.univ.image X).card : ℝ))) :=
    Finset.sum_congr rfl (fun v hv => by rw [hprob v hv])
  unfold uniformEntropy
  rw [hsum, Finset.sum_const, nsmul_eq_mul, one_div, Real.log_inv]
  field_simp

/-- Entropy is invariant under relabelling the sample space by a bijection. -/
theorem uniformProb_comp_equiv {Ω' : Type*} [Fintype Ω'] (e : Ω' ≃ Ω) (X : Ω → V) (v : V) :
    uniformProb (X ∘ e) v = uniformProb X v := by
  unfold uniformProb
  have h1 : (Finset.univ.filter (fun ω' => (X ∘ e) ω' = v)).card =
      (Finset.univ.filter (fun ω => X ω = v)).card := by
    rw [← Fintype.card_subtype, ← Fintype.card_subtype]
    exact Fintype.card_congr (e.subtypeEquiv (fun _ => Iff.rfl))
  rw [h1, Fintype.card_congr e]

theorem image_comp_equiv {Ω' : Type*} [Fintype Ω'] (e : Ω' ≃ Ω) (X : Ω → V) :
    Finset.univ.image (X ∘ e) = Finset.univ.image X := by
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp]
  constructor
  · rintro ⟨ω', rfl⟩
    exact ⟨e ω', rfl⟩
  · rintro ⟨ω, rfl⟩
    exact ⟨e.symm ω, by simp⟩

theorem uniformEntropy_comp_equiv {Ω' : Type*} [Fintype Ω'] (e : Ω' ≃ Ω) (X : Ω → V) :
    uniformEntropy (X ∘ e) = uniformEntropy X := by
  unfold uniformEntropy
  rw [image_comp_equiv e X]
  exact Finset.sum_congr rfl (fun v _ => by rw [uniformProb_comp_equiv e X v])

end Entropy

/-! ### Maps that factor injectively through the first factor of a product -/

section Product

variable {A B : Type*} {Ω : Type*} [Fintype Ω] {V : Type*} [DecidableEq V]

/-- The fibre of `ω ↦ (e ω).1` over `a` is a copy of `B`. -/
def fibreEquiv (e : Ω ≃ A × B) (a : A) : {ω : Ω // (e ω).1 = a} ≃ B where
  toFun ω := (e ω.1).2
  invFun b := ⟨e.symm (a, b), by simp⟩
  left_inv ω := by
    apply Subtype.ext
    have h : e ω.1 = (a, (e ω.1).2) := Prod.ext ω.2 rfl
    show e.symm (a, (e ω.1).2) = ω.1
    rw [← h, e.symm_apply_apply]
  right_inv b := by simp

theorem fibre_card_fst [Fintype B] [DecidableEq A] (e : Ω ≃ A × B) (ψ : A → V)
    (hψ : Function.Injective ψ) (ω₀ : Ω) :
    (Finset.univ.filter (fun ω => ψ (e ω).1 = ψ (e ω₀).1)).card = Fintype.card B := by
  have hfilter : (Finset.univ.filter (fun ω => ψ (e ω).1 = ψ (e ω₀).1)) =
      Finset.univ.filter (fun ω => (e ω).1 = (e ω₀).1) := by
    ext ω
    simp [hψ.eq_iff]
  rw [hfilter, ← Fintype.card_subtype]
  exact Fintype.card_congr (fibreEquiv e (e ω₀).1)

theorem image_card_fst [Fintype A] [Nonempty B] [DecidableEq A] (e : Ω ≃ A × B) (ψ : A → V)
    (hψ : Function.Injective ψ) :
    (Finset.univ.image (fun ω => ψ (e ω).1)).card = Fintype.card A := by
  have hsurj : Function.Surjective (fun ω : Ω => (e ω).1) := by
    intro a
    obtain ⟨b⟩ := ‹Nonempty B›
    exact ⟨e.symm (a, b), by simp⟩
  have himg : Finset.univ.image (fun ω => ψ (e ω).1) = Finset.univ.image ψ := by
    rw [show (fun ω : Ω => ψ (e ω).1) = ψ ∘ (fun ω => (e ω).1) from rfl,
      ← Finset.image_image, Finset.image_univ_of_surjective hsurj]
  rw [himg, Finset.card_image_of_injective _ hψ, Finset.card_univ]

/-- A map of the form `ω ↦ ψ ((e ω).1)` with `ψ` injective is uniform on
`|A|` values; its entropy is `log |A|`. -/
theorem uniformEntropy_fst [Fintype A] [Fintype B] [Nonempty B] [DecidableEq A] [Nonempty Ω]
    (e : Ω ≃ A × B) (ψ : A → V)
    (hψ : Function.Injective ψ) :
    uniformEntropy (fun ω => ψ (e ω).1) = Real.log (Fintype.card A : ℝ) := by
  rw [uniformEntropy_of_const_fibre _ (Fintype.card B) Fintype.card_pos ?_,
    image_card_fst e ψ hψ]
  intro v hv
  obtain ⟨ω₀, -, rfl⟩ := Finset.mem_image.1 hv
  exact fibre_card_fst e ψ hψ ω₀

end Product

/-! ### The five-cycle construction -/

section FiveCycle

open TermCoding.Examples.C5

theorem mem_N_left {S : Finset (Fin 5)} {s : Fin 5} (hs : s ∈ S) : s ∈ N S :=
  Finset.mem_union_left _ hs

theorem mem_N_right {S : Finset (Fin 5)} {s : Fin 5} (hs : s ∈ S) : s + 1 ∈ N S :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs)

/-- Reading the coordinates `X_s = (U_s, U_{s+1})`, `s ∈ S`, off the values
`U_j`, `j ∈ N S`. -/
def readOff (S : Finset (Fin 5)) {B : Type} (a : {j // j ∈ N S} → B) :
    {s // s ∈ S} → B × B :=
  fun s => (a ⟨s.1, mem_N_left s.2⟩, a ⟨s.1 + 1, mem_N_right s.2⟩)

theorem readOff_injective (S : Finset (Fin 5)) {B : Type} :
    Function.Injective (readOff S (B := B)) := by
  intro a a' h
  funext j
  rcases j with ⟨j, hj⟩
  rcases Finset.mem_union.1 hj with hj' | hj'
  · exact congrArg Prod.fst (congrFun h ⟨j, hj'⟩)
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hj'
    exact congrArg Prod.snd (congrFun h ⟨s, hs⟩)

/-- Projection of a configuration to the coordinates in `S`. -/
def projS (S : Finset (Fin 5)) {B : Type} (a : Assignment Var (B × B)) :
    {s // s ∈ S} → B × B :=
  fun s => a (vertex s.1)

theorem cycleAssignment_vertex {B : Type} (u : Fin 5 → B) (i : Fin 5) :
    cycleAssignment u (vertex i) = (u i, u (i + 1)) := by
  fin_cases i <;> rfl

/-- The winning configurations of `pairStrategy` are exactly the
configurations `X_i = (U_i, U_{i+1})`. -/
theorem wins_iff_exists_cycle {B : Type} (a : Assignment Var (B × B)) :
    TermSystem.Wins system pairStrategy a ↔ ∃ u : Fin 5 → B, a = cycleAssignment u := by
  constructor
  · intro hw
    refine ⟨fun i => (a (vertex i)).1, ?_⟩
    have h0 := hw 0
    have h1 := hw 1
    have h2 := hw 2
    have h3 := hw 3
    have h4 := hw 4
    simp [system, pairStrategy, SDOSExponents.binaryInput, SDOSExponents.binaryEquation]
      at h0 h1 h2 h3 h4
    funext v
    cases v
    · exact Prod.ext rfl (congrArg Prod.snd h0).symm
    · exact Prod.ext rfl (congrArg Prod.snd h1).symm
    · exact Prod.ext rfl (congrArg Prod.snd h2).symm
    · exact Prod.ext rfl (congrArg Prod.snd h3).symm
    · exact Prod.ext rfl (congrArg Prod.snd h4).symm
  · rintro ⟨u, rfl⟩
    exact cycleAssignment_wins u

/-- The winning set of the square-alphabet strategy. -/
abbrev Winners (B : Type) :=
  {a : Assignment Var (B × B) // TermSystem.Wins system pairStrategy a}

noncomputable instance winnersFintype (B : Type) [Fintype B] : Fintype (Winners B) :=
  Fintype.ofFinite _

/-- `u ↦ (X_i = (u_i, u_{i+1}))_i` is a bijection onto the winning set. -/
noncomputable def cycleEquiv (B : Type) : (Fin 5 → B) ≃ Winners B :=
  Equiv.ofBijective (fun u => ⟨cycleAssignment u, cycleAssignment_wins u⟩)
    ⟨cycleWinningEmbedding.injective, fun w => by
      obtain ⟨u, hu⟩ := (wins_iff_exists_cycle w.1).1 w.2
      exact ⟨u, Subtype.ext hu.symm⟩⟩

instance winnersNonempty (B : Type) [Nonempty B] : Nonempty (Winners B) :=
  ⟨cycleEquiv B (fun _ => Classical.arbitrary B)⟩

/-- There are exactly `m^5` winning configurations on the square alphabet
`[m] × [m]`. -/
theorem card_winners (m : ℕ) : Fintype.card (Winners (Fin m)) = m ^ 5 := by
  rw [← Fintype.card_congr (cycleEquiv (Fin m)), Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin]

/-- The coordinate projection to `S` factors injectively through the
restriction of `u` to `N S`. -/
theorem projS_comp_cycleEquiv (S : Finset (Fin 5)) (B : Type) :
    (fun w : Winners B => projS S w.1) ∘ (cycleEquiv B) =
      fun u : Fin 5 → B =>
        readOff S ((Equiv.piEquivPiSubtypeProd (fun j => j ∈ N S) (fun _ => B)) u).1 := by
  funext u
  funext s
  show projS S (cycleAssignment u) s = _
  unfold projS readOff
  simp only [Equiv.piEquivPiSubtypeProd_apply]
  exact cycleAssignment_vertex u s.1

/-- **Entropy of the coordinate projection.**  Under the uniform distribution
on the winning set, `H(X_S) = |N S| · log m`. -/
theorem uniformEntropy_projS (S : Finset (Fin 5)) (m : ℕ) [NeZero m] :
    uniformEntropy (fun w : Winners (Fin m) => projS S w.1) =
      ((N S).card : ℝ) * Real.log (m : ℝ) := by
  rw [← uniformEntropy_comp_equiv (cycleEquiv (Fin m)), projS_comp_cycleEquiv,
    uniformEntropy_fst _ _ (readOff_injective S)]
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Nat.cast_pow, Real.log_pow]

/-- **`hstar` is an entropy vector.**  For `n = m²`, the base-`n` entropy
`H(X_S) / log n` of the coordinate projection equals `hstar S`. -/
theorem hstar_eq_normalisedEntropy (S : Finset (Fin 5)) (m : ℕ) (hm : 2 ≤ m) :
    uniformEntropy (fun w : Winners (Fin m) => projS S w.1) / Real.log ((m : ℝ) ^ 2) =
      hstar S := by
  haveI : NeZero m := ⟨by omega⟩
  rw [uniformEntropy_projS S m, Real.log_pow]
  have hlog : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm)
  unfold hstar
  field_simp
  ring

/-- Proposition 7.1 assembled: the unique maximiser of `h [5]` over `P5` is the
non-integer vertex `hstar`, and `hstar` is the normalised entropy vector of
the uniform distribution on the `m^5` winning configurations of the
square-alphabet construction, for every `m ≥ 2`. -/
theorem five_cycle_entropy_vertex :
    (∀ h ∈ P5, h Finset.univ ≤ 5 / 2) ∧ hstar ∈ P5 ∧ hstar Finset.univ = 5 / 2 ∧
    (∀ h ∈ P5, h Finset.univ = 5 / 2 → h = hstar) ∧
    hstar ∈ Set.extremePoints ℝ P5 ∧ (∀ z : ℤ, (z : ℝ) ≠ hstar {0, 1}) ∧
    (∀ (m : ℕ), 2 ≤ m → Fintype.card (Winners (Fin m)) = m ^ 5 ∧
      ∀ S : Finset (Fin 5),
        uniformEntropy (fun w : Winners (Fin m) => projS S w.1) / Real.log ((m : ℝ) ^ 2) =
          hstar S) :=
  ⟨le_five_halves, hstar_mem, hstar_univ, eq_hstar_of_max, hstar_extreme,
    hstar_pair_not_integer,
    fun m hm => ⟨card_winners m, fun S => hstar_eq_normalisedEntropy S m hm⟩⟩

end FiveCycle

end TermCoding.Examples.C5Entropy
