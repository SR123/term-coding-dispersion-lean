import TermCoding.Dispersion.Basic
import TermCoding.Dispersion.TermCut
import TermCoding.FiniteFlattening
import Mathlib.Data.Fintype.Prod

/-!
# The dynamic-routing lower bound (Riis–Gadouleau 2019, Definition 9 / Lemma 4)

This module formalises the *lower-bound construction* of the 2019 source in
certificate form.  A `DagPath` is a path in the shared term DAG of an
instance `t` from an input variable to an output term (each node a direct
child of the next); a `PathSystem t q` is a family of `q` pairwise
vertex-disjoint such paths.

Given a path system, the source's "dynamic routing" interpretation is built
on the tagged alphabet `Sub t × Fin m`, where `Sub t` is the finite set of
subterms of `t`: a value `(u, β)` means "block value `β` belonging to
subterm `u`".  Every operation table reads the tags of its arguments,
reconstructs the subterm it is computing, and forwards the block value along
the unique path through that subterm (repeated symbols therefore need no
gadget: one global table routes correctly at every occurrence).

Results (all kernel-checked, unconditional):

* `eval_routing` -- under the routing interpretation, every subterm `u`
  of `t` evaluates to `(u, routeBlock u)`: on-path subterms carry their
  path's block value.
* `pathSystem_pow_le_dispN` -- `m^q ≤ Disp_{s·m}(t)` where
  `s = |Sub t|` (the source's Lemma 4, with `|B| = m`).
* `pathSystem_lowerBound_real` -- hence `Disp_n(t) ≥ n^q/(2s)^q` for all
  `n ≥ 2s`: the `Θ`-form lower bound with exponent `q`.
* `pathSystem_card_le_termCutNumber` -- weak duality: every term-cut meets
  every path, so `q ≤ ρ(t)`.

Consequently (`Conditional/MaxFlowExponent.lean`), the external input for
`thm:disp-exponent` shrinks to **Menger's theorem** for the term DAG
(`MengerForTerms t`: a path system of size `ρ(t)` exists), a classical
graph-theoretic fact; for any concrete instance it can be discharged by
exhibiting the paths.
-/

namespace TermCoding

namespace Dispersion

universe uSym

variable {σ : Signature.{uSym}} {k r : Nat}

/-! ### The term DAG -/

/-- `u` is a direct child of `v` in the term DAG. -/
def DirectChild (u v : Term σ (Fin k)) : Prop :=
  ∃ (s : σ.Symbol) (args : Fin (σ.arity s) → Term σ (Fin k)) (p : Fin (σ.arity s)),
    v = .app s args ∧ args p = u

theorem DirectChild.size_lt {u v : Term σ (Fin k)} (h : DirectChild u v) :
    u.size < v.size := by
  obtain ⟨s, args, p, rfl, rfl⟩ := h
  simp only [Term.size]
  have hle := Finset.single_le_sum (f := fun q => (args q).size)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)
  simp only at hle
  omega

/-- The finite set of subterms of all output terms of `t` (the source's
`Γ_sub`). -/
noncomputable def instanceSubterms (t : Instance σ k r) : Finset (Term σ (Fin k)) := by
  classical
  exact Finset.univ.biUnion (fun i => (t i).subterms)

theorem output_mem_instanceSubterms (t : Instance σ k r) (i : Fin r) :
    t i ∈ instanceSubterms t := by
  classical
  unfold instanceSubterms
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Term.self_mem_subterms (t i)⟩

theorem mem_instanceSubterms_of_child {t : Instance σ k r}
    {u v : Term σ (Fin k)} (hv : v ∈ instanceSubterms t) (h : DirectChild u v) :
    u ∈ instanceSubterms t := by
  classical
  obtain ⟨s, args, p, rfl, rfl⟩ := h
  unfold instanceSubterms at hv ⊢
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hv
  exact Finset.mem_biUnion.mpr
    ⟨i, Finset.mem_univ i,
      Term.subterms_subset_of_mem hi (Term.child_mem_subterms s args p)⟩

/-! ### Paths and path systems -/

/-- A path in the term DAG of `t` from the input variable `source` to the
output term `t out`, with `len` edges; `node j` for `j ≤ len` are its
vertices (values above `len` are irrelevant). -/
structure DagPath (t : Instance σ k r) where
  /-- Number of edges. -/
  len : ℕ
  /-- The vertices (only positions `0..len` matter). -/
  node : ℕ → Term σ (Fin k)
  /-- The input variable at which the path starts. -/
  source : Fin k
  /-- The output coordinate at which the path ends. -/
  out : Fin r
  first : node 0 = .var source
  last : node len = t out
  step : ∀ j, j < len → DirectChild (node j) (node (j + 1))

namespace DagPath

variable {t : Instance σ k r} (P : DagPath t)

theorem size_lt_of_lt {i j : ℕ} (hij : i < j) (hj : j ≤ P.len) :
    (P.node i).size < (P.node j).size := by
  induction j with
  | zero => omega
  | succ j ih =>
      have hstep : (P.node j).size < (P.node (j + 1)).size :=
        (P.step j (by omega)).size_lt
      rcases Nat.lt_succ_iff_lt_or_eq.mp hij with hlt | rfl
      · exact lt_trans (ih hlt (by omega)) hstep
      · exact hstep

/-- Within a path, positions `≤ len` carry pairwise distinct vertices. -/
theorem node_injOn {i j : ℕ} (hi : i ≤ P.len) (hj : j ≤ P.len)
    (h : P.node i = P.node j) : i = j := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · exact absurd (congrArg Term.size h) (Nat.ne_of_lt (P.size_lt_of_lt hlt hj))
  · exact heq
  · exact absurd (congrArg Term.size h.symm) (Nat.ne_of_lt (P.size_lt_of_lt hgt hi))

/-- Every path vertex is a subterm of `t`. -/
theorem node_mem : ∀ d j, j + d = P.len → P.node j ∈ instanceSubterms t := by
  intro d
  induction d with
  | zero =>
      intro j hj
      have : j = P.len := by omega
      subst this
      rw [P.last]
      exact output_mem_instanceSubterms t P.out
  | succ d ih =>
      intro j hj
      have hnext : P.node (j + 1) ∈ instanceSubterms t := ih (j + 1) (by omega)
      exact mem_instanceSubterms_of_child hnext (P.step j (by omega))

theorem node_mem_of_le {j : ℕ} (hj : j ≤ P.len) :
    P.node j ∈ instanceSubterms t :=
  P.node_mem (P.len - j) j (by omega)

end DagPath

/-- A family of `q` pairwise vertex-disjoint paths. -/
structure PathSystem (t : Instance σ k r) (q : ℕ) where
  path : Fin q → DagPath t
  disjoint : ∀ a b : Fin q, ∀ ja jb, ja ≤ (path a).len → jb ≤ (path b).len →
    (path a).node ja = (path b).node jb → a = b

namespace PathSystem

variable {t : Instance σ k r} {q : ℕ} (P : PathSystem t q)

/-- A vertex lies on at most one path, at a unique position. -/
theorem position_unique {a b : Fin q} {ja jb : ℕ}
    (ha : ja ≤ (P.path a).len) (hb : jb ≤ (P.path b).len)
    (h : (P.path a).node ja = (P.path b).node jb) : a = b ∧ ja = jb := by
  have hab : a = b := P.disjoint a b ja jb ha hb h
  subst hab
  exact ⟨rfl, (P.path a).node_injOn ha hb h⟩

/-- Distinct paths end at distinct outputs. -/
theorem out_injective : Function.Injective (fun a => (P.path a).out) := by
  intro a b hab
  simp only at hab
  apply P.disjoint a b (P.path a).len (P.path b).len le_rfl le_rfl
  rw [(P.path a).last, (P.path b).last, hab]

end PathSystem

/-! ### The routing interpretation -/

/-- The tag alphabet: subterms of `t`. -/
abbrev Sub (t : Instance σ k r) := {u : Term σ (Fin k) // u ∈ instanceSubterms t}

/-- The block value routed to a subterm: its path's value if it lies on a
path, `d` otherwise. -/
noncomputable def routeBlock {t : Instance σ k r} {q : ℕ} (P : PathSystem t q)
    {m : ℕ} (b : Fin q → Fin m) (d : Fin m) (u : Term σ (Fin k)) : Fin m := by
  classical
  exact if h : ∃ aj : Fin q × ℕ, aj.2 ≤ (P.path aj.1).len ∧ (P.path aj.1).node aj.2 = u
    then b (Classical.choose h).1 else d

theorem routeBlock_eq_of_node {t : Instance σ k r} {q : ℕ} (P : PathSystem t q)
    {m : ℕ} (b : Fin q → Fin m) (d : Fin m) {u : Term σ (Fin k)} (a : Fin q)
    {j : ℕ} (hj : j ≤ (P.path a).len) (hn : (P.path a).node j = u) :
    routeBlock P b d u = b a := by
  classical
  unfold routeBlock
  have h : ∃ aj : Fin q × ℕ, aj.2 ≤ (P.path aj.1).len ∧ (P.path aj.1).node aj.2 = u :=
    ⟨(a, j), hj, hn⟩
  rw [dif_pos h]
  have hspec := Classical.choose_spec h
  have := P.position_unique hspec.1 hj (hspec.2.trans hn.symm)
  rw [this.1]

theorem routeBlock_eq_default {t : Instance σ k r} {q : ℕ} (P : PathSystem t q)
    {m : ℕ} (b : Fin q → Fin m) (d : Fin m) {u : Term σ (Fin k)}
    (h : ¬ ∃ aj : Fin q × ℕ, aj.2 ≤ (P.path aj.1).len ∧ (P.path aj.1).node aj.2 = u) :
    routeBlock P b d u = d := by
  classical
  unfold routeBlock
  rw [dif_neg h]

/-- The input assignment carrying the block values `b` at the path sources
(and consistent tags everywhere a variable is a subterm). -/
noncomputable def taggedAssignment {t : Instance σ k r} {q : ℕ} (P : PathSystem t q)
    (m : ℕ) (d : Sub t × Fin m) (b : Fin q → Fin m) : Fin k → Sub t × Fin m :=
  fun v => by
    classical
    exact if h : (Term.var v : Term σ (Fin k)) ∈ instanceSubterms t
      then (⟨.var v, h⟩, routeBlock P b d.2 (.var v)) else d

/-- The dynamic-routing interpretation: one total table per symbol.  It
reconstructs the subterm being computed from the argument tags and forwards
the block value of the path predecessor. -/
noncomputable def routingInterpretation {t : Instance σ k r} {q : ℕ}
    (P : PathSystem t q) (m : ℕ) (d : Sub t × Fin m) :
    Interpretation σ (Sub t × Fin m) := fun s input => by
  classical
  exact
    if hc : (Term.app s (fun p => (input p).1.1) : Term σ (Fin k)) ∈ instanceSubterms t then
      if hp : ∃ aj : Fin q × ℕ, aj.2 + 1 ≤ (P.path aj.1).len ∧
          (P.path aj.1).node (aj.2 + 1) = Term.app s (fun p => (input p).1.1) then
        if hq : ∃ p, (input p).1.1 =
            (P.path (Classical.choose hp).1).node (Classical.choose hp).2 then
          (⟨_, hc⟩, (input (Classical.choose hq)).2)
        else (⟨_, hc⟩, d.2)
      else (⟨_, hc⟩, d.2)
    else d

/-- The key evaluation lemma: under the routing interpretation, every
subterm of `t` evaluates to itself (as a tag) together with its routed
block value.  Structural induction; repeated symbols, repeated arguments,
constants and shared subterms are all handled by the one global table. -/
theorem eval_routing {t : Instance σ k r} {q : ℕ} (P : PathSystem t q)
    (m : ℕ) (d : Sub t × Fin m) (b : Fin q → Fin m) :
    ∀ u : Term σ (Fin k), ∀ hu : u ∈ instanceSubterms t,
      u.eval (routingInterpretation P m d) (taggedAssignment P m d b) =
        (⟨u, hu⟩, routeBlock P b d.2 u)
  | .var v, hu => by
      classical
      show taggedAssignment P m d b v = _
      unfold taggedAssignment
      rw [dif_pos hu]
  | .app s args, hu => by
      classical
      have hmem : ∀ p, args p ∈ instanceSubterms t :=
        fun p => mem_instanceSubterms_of_child hu ⟨s, args, p, rfl, rfl⟩
      have ih : ∀ p, (args p).eval (routingInterpretation P m d) (taggedAssignment P m d b) =
          (⟨args p, hmem p⟩, routeBlock P b d.2 (args p)) :=
        fun p => eval_routing P m d b (args p) (hmem p)
      show routingInterpretation P m d s
          (fun p => (args p).eval (routingInterpretation P m d) (taggedAssignment P m d b)) = _
      rw [show (fun p => (args p).eval (routingInterpretation P m d) (taggedAssignment P m d b)) =
          (fun p => ((⟨args p, hmem p⟩ : Sub t), routeBlock P b d.2 (args p))) from funext ih]
      unfold routingInterpretation
      rw [dif_pos hu]
      by_cases hp : ∃ aj : Fin q × ℕ, aj.2 + 1 ≤ (P.path aj.1).len ∧
          (P.path aj.1).node (aj.2 + 1) = Term.app s args
      · rw [dif_pos hp]
        obtain ⟨hlen, hnode⟩ := Classical.choose_spec hp
        obtain ⟨s', args', p', happ, harg⟩ :=
          (P.path (Classical.choose hp).1).step (Classical.choose hp).2 (by omega)
        rw [hnode] at happ
        injection happ with hs hargs
        subst hs
        have hargs' := eq_of_heq hargs
        subst hargs'
        have hq : ∃ p, (((⟨args p, hmem p⟩ : Sub t), routeBlock P b d.2 (args p)) : Sub t × Fin m).1.1 =
            (P.path (Classical.choose hp).1).node (Classical.choose hp).2 := ⟨p', harg⟩
        rw [dif_pos hq]
        have hchosen := Classical.choose_spec hq
        have hblock : routeBlock P b d.2 (args (Classical.choose hq)) = b (Classical.choose hp).1 :=
          routeBlock_eq_of_node P b d.2 (Classical.choose hp).1
            (j := (Classical.choose hp).2) (by omega) hchosen.symm
        have htop : routeBlock P b d.2 (Term.app s args) = b (Classical.choose hp).1 :=
          routeBlock_eq_of_node P b d.2 (Classical.choose hp).1
            (j := (Classical.choose hp).2 + 1) hlen hnode
        rw [htop]
        exact Prod.ext rfl hblock
      · rw [dif_neg hp]
        -- not an internal path node; position 0 is a variable, so not on a path at all
        have hnot : ¬ ∃ aj : Fin q × ℕ, aj.2 ≤ (P.path aj.1).len ∧
            (P.path aj.1).node aj.2 = Term.app s args := by
          rintro ⟨⟨a, j⟩, hj, hn⟩
          cases j with
          | zero =>
              rw [(P.path a).first] at hn
              exact Term.noConfusion hn
          | succ j' => exact hp ⟨(a, j'), hj, hn⟩
        rw [routeBlock_eq_default P b d.2 hnot]

/-! ### The image lower bound -/

section Counting

variable {t : Instance σ k r} {q : ℕ}

/-- The routed assignments realise `m^q` distinct outputs: the block values
can be read off at the path outputs. -/
theorem injective_routedOutputs (P : PathSystem t q) (m : ℕ) (d : Sub t × Fin m) :
    Function.Injective (fun b : Fin q → Fin m =>
      termMap t (routingInterpretation P m d) (taggedAssignment P m d b)) := by
  intro b b' h
  funext a
  have ha := congrFun h (P.path a).out
  simp only [termMap] at ha
  have h1 := eval_routing P m d b (t (P.path a).out)
    (output_mem_instanceSubterms t (P.path a).out)
  have h2 := eval_routing P m d b' (t (P.path a).out)
    (output_mem_instanceSubterms t (P.path a).out)
  rw [h1, h2] at ha
  have hb := congrArg Prod.snd ha
  simp only at hb
  rwa [routeBlock_eq_of_node P b d.2 a le_rfl (P.path a).last,
    routeBlock_eq_of_node P b' d.2 a le_rfl (P.path a).last] at hb

/-- Lemma 4 of the source, in cardinal form: the routing interpretation has
image of size at least `m^q`. -/
theorem pow_le_imageCard_routing (P : PathSystem t q) (m : ℕ) (d : Sub t × Fin m) :
    m ^ q ≤ imageCard t (routingInterpretation P m d) := by
  classical
  unfold imageCard
  haveI : Finite ↥(Set.range (termMap t (routingInterpretation P m d))) :=
    (Set.finite_range _).to_subtype
  let φ : (Fin q → Fin m) → Set.range (termMap t (routingInterpretation P m d)) :=
    fun b => ⟨termMap t (routingInterpretation P m d) (taggedAssignment P m d b),
      ⟨taggedAssignment P m d b, rfl⟩⟩
  have hφ : Function.Injective φ := by
    intro b b' h
    exact injective_routedOutputs P m d (congrArg Subtype.val h)
  calc m ^ q = Nat.card (Fin q → Fin m) := by
        rw [Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        simp
    _ ≤ Nat.card ↥(Set.range (termMap t (routingInterpretation P m d))) :=
        Nat.card_le_card_of_injective φ hφ

/-- `m^q ≤ Disp_{s·m}(t)` where `s = |Sub t|` and `m ≥ 1` (the source's
lower bound at alphabet size `s·m`). -/
theorem pathSystem_pow_le_dispN [Fintype σ.Symbol] (P : PathSystem t q)
    (hr : 0 < r) (m : ℕ) (hm : 1 ≤ m) :
    m ^ q ≤ dispN t ((instanceSubterms t).card * m) := by
  classical
  have hd : Nonempty (Sub t × Fin m) := by
    refine ⟨⟨⟨t ⟨0, hr⟩, output_mem_instanceSubterms t ⟨0, hr⟩⟩, ⟨0, by omega⟩⟩⟩
  obtain ⟨d⟩ := hd
  have h1 := pow_le_imageCard_routing P m d
  have h2 := imageCard_le_disp (A := Sub t × Fin m) t (routingInterpretation P m d)
  have h3 := disp_eq_dispN (A := Sub t × Fin m) t
  rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin] at h3
  omega

/-- The `Θ`-form lower bound with exponent `q`:
`Disp_n(t) ≥ (2s)^{-q}·n^q` for all `n ≥ 2s`. -/
theorem pathSystem_lowerBound_real [Fintype σ.Symbol] (P : PathSystem t q) (hr : 0 < r) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n, N ≤ n → c * (n : ℝ) ^ q ≤ dispN t n := by
  classical
  set s := (instanceSubterms t).card with hs
  have hs1 : 1 ≤ s := by
    rw [hs]
    exact Finset.card_pos.mpr ⟨t ⟨0, hr⟩, output_mem_instanceSubterms t ⟨0, hr⟩⟩
  refine ⟨(1 / (2 * s : ℝ)) ^ q, by positivity, 2 * s, ?_⟩
  intro n hn
  have hm1 : 1 ≤ n / s := (Nat.one_le_div_iff (by omega)).mpr (by omega)
  have hnat : (n / s) ^ q ≤ dispN t (s * (n / s)) := pathSystem_pow_le_dispN P hr (n / s) hm1
  have hmono : dispN t (s * (n / s)) ≤ dispN t n := by
    have hpos : 0 < s * (n / s) := Nat.mul_pos (by omega) (by omega)
    exact dispN_mono t (by omega) (Nat.mul_div_le n s)
  have hdiv : (n : ℝ) / (2 * s) ≤ ((n / s : ℕ) : ℝ) := by
    have h1 : n < s * (n / s) + s := by
      have h0 := Nat.lt_mul_div_succ n (show 0 < s by omega)
      rw [Nat.mul_add, Nat.mul_one] at h0
      exact h0
    have h2 : (n : ℝ) < s * ((n / s : ℕ) : ℝ) + s := by exact_mod_cast h1
    have hd1 : (1 : ℝ) ≤ ((n / s : ℕ) : ℝ) := by exact_mod_cast hm1
    have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hq : ((n / s : ℕ) : ℝ) ^ q ≤ (dispN t n : ℝ) := by
    have : ((n / s) ^ q : ℕ) ≤ dispN t n := le_trans hnat hmono
    exact_mod_cast this
  calc (1 / (2 * s : ℝ)) ^ q * (n : ℝ) ^ q
      = ((n : ℝ) / (2 * s)) ^ q := by
        rw [div_pow, div_pow, one_pow]
        ring
    _ ≤ ((n / s : ℕ) : ℝ) ^ q := pow_le_pow_left₀ (by positivity) hdiv q
    _ ≤ (dispN t n : ℝ) := hq

end Counting

/-! ### Weak duality: paths meet every term-cut -/

/-- Every path from a variable to an expressible output meets the cut. -/
theorem DagPath.exists_node_mem_cut {t : Instance σ k r} (Q : DagPath t)
    (C : Finset (Term σ (Fin k))) :
    ∀ j, j ≤ Q.len → ExprFrom (↑C) (Q.node j) → ∃ j' ≤ j, Q.node j' ∈ C := by
  intro j
  induction j with
  | zero =>
      intro _ hexpr
      rw [Q.first] at hexpr
      exact ⟨0, le_rfl, by rw [Q.first]; exact Finset.mem_coe.mp hexpr.var_mem⟩
  | succ j ih =>
      intro hj hexpr
      obtain ⟨s, args, p, happ, harg⟩ := Q.step j (by omega)
      rw [happ] at hexpr
      rcases hexpr.app_inv with hmem | hall
      · exact ⟨j + 1, le_rfl, by rw [happ]; exact hmem⟩
      · have hprev : ExprFrom (↑C) (Q.node j) := by
          rw [← harg]
          exact hall p
        obtain ⟨j', hj', hmem⟩ := ih (by omega) hprev
        exact ⟨j', by omega, hmem⟩

/-- Weak duality: a system of `q` disjoint paths forces every term-cut to
have at least `q` elements; hence `q ≤ ρ(t)`. -/
theorem pathSystem_card_le_of_termCut {t : Instance σ k r} {q : ℕ}
    (P : PathSystem t q) (C : Finset (Term σ (Fin k))) (hC : IsTermCut t C) :
    q ≤ C.card := by
  classical
  -- choose a cut vertex on each path
  have hhit : ∀ a : Fin q, ∃ j ≤ (P.path a).len, (P.path a).node j ∈ C := by
    intro a
    apply (P.path a).exists_node_mem_cut C (P.path a).len le_rfl
    rw [(P.path a).last]
    exact hC (P.path a).out
  let hit : Fin q → {u : Term σ (Fin k) // u ∈ C} := fun a =>
    ⟨(P.path a).node (Classical.choose (hhit a)),
      (Classical.choose_spec (hhit a)).2⟩
  have hinj : Function.Injective hit := by
    intro a b hab
    have h := congrArg Subtype.val hab
    simp only [hit] at h
    exact P.disjoint a b _ _ (Classical.choose_spec (hhit a)).1
      (Classical.choose_spec (hhit b)).1 h
  have := Fintype.card_le_of_injective hit hinj
  simpa [Fintype.card_coe] using this

theorem pathSystem_card_le_termCutNumber {t : Instance σ k r} {q : ℕ}
    (P : PathSystem t q) : q ≤ termCutNumber t := by
  obtain ⟨C, hC, hcard⟩ := exists_termCut_card_eq t
  rw [← hcard]
  exact pathSystem_card_le_of_termCut P C hC

/-- Menger's theorem for the term DAG of `t`, as a per-instance statement:
some family of `ρ(t)` pairwise vertex-disjoint variable-to-output paths
exists.  (Classical; the reverse inequality is
`pathSystem_card_le_termCutNumber`.)  This is the only external ingredient
still needed for the `Θ(n^{ρ(t)})` lower bound. -/
def MengerForTerms (t : Instance σ k r) : Prop :=
  Nonempty (PathSystem t (termCutNumber t))

/-! ### A worked certificate: the diamond -/

/-- A one-edge path from an input variable directly into an output term. -/
def singleEdgePath (t : Instance σ k r) (v : Fin k) (i : Fin r)
    (h : DirectChild (.var v) (t i)) : DagPath t where
  len := 1
  node := fun j => if j = 0 then .var v else t i
  source := v
  out := i
  first := by simp
  last := by simp
  step := by
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    simpa using h

@[simp] theorem singleEdgePath_len (t : Instance σ k r) (v : Fin k) (i : Fin r)
    (h : DirectChild (.var v) (t i)) : (singleEdgePath t v i h).len = 1 := rfl

theorem singleEdgePath_node (t : Instance σ k r) (v : Fin k) (i : Fin r)
    (h : DirectChild (.var v) (t i)) (j : ℕ) :
    (singleEdgePath t v i h).node j = if j = 0 then .var v else t i := rfl

set_option linter.unusedSimpArgs false in
/-- The four vertex-disjoint paths `x→f(x,y)`, `z→f(x,z)`, `y→f(y,w)`,
`w→f(z,w)` of the diamond: the flow certificate of `lem:diamond-maxflow`,
valid in the source's vertex-capacitated model. -/
def diamondPathSystem : PathSystem diamond 4 where
  path := ![singleEdgePath diamond 0 0 ⟨(), ![.var 0, .var 1], (0 : Fin 2), rfl, rfl⟩,
    singleEdgePath diamond 2 1 ⟨(), ![.var 0, .var 2], (1 : Fin 2), rfl, rfl⟩,
    singleEdgePath diamond 1 2 ⟨(), ![.var 1, .var 3], (0 : Fin 2), rfl, rfl⟩,
    singleEdgePath diamond 3 3 ⟨(), ![.var 2, .var 3], (1 : Fin 2), rfl, rfl⟩]
  disjoint := by
    intro a b ja jb hja hjb h
    fin_cases a <;> fin_cases b <;> first
      | rfl
      | (exfalso
         replace hja : ja ≤ 1 := hja
         replace hjb : jb ≤ 1 := hjb
         interval_cases ja <;> interval_cases jb <;>
           simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val,
             singleEdgePath_node, if_true, if_pos, if_neg, one_ne_zero,
             reduceIte] at h <;>
           first
             | exact Term.noConfusion h
             | (injection h with h1
                exact absurd h1 (by decide))
             | (injection h with h1 h2
                have h4 := congrFun h2 (0 : Fin 2)
                have h5 := congrFun h2 (1 : Fin 2)
                simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h4 h5
                first
                  | (injection h4 with h6
                     exact absurd h6 (by decide))
                  | (injection h5 with h6
                     exact absurd h6 (by decide))))

/-- Menger's equality holds for the diamond, by the explicit certificate. -/
theorem mengerForTerms_diamond : MengerForTerms diamond := by
  unfold MengerForTerms
  rw [termCutNumber_diamond]
  exact ⟨diamondPathSystem⟩

end Dispersion

end TermCoding
