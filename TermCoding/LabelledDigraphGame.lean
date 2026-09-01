import TermCoding.LabelledDependencyGraph
import TermCoding.Asymptotics
import TermCoding.Alphabet
import TermCoding.Exponent

/-!
# Guessing games on arbitrary finite labelled digraphs

Paper 1 (journal version) states Definitions 5.1/5.3/5.9, Proposition 5.5,
Theorem 5.6 and Corollary 6.3 for an *arbitrary* finite labelled digraph
`(G, λ, S)`.  The Paper 1 Lean development proves the numerical statements
(monotonicity, product lower bound, convergence of the guessing rate) for the
occurrence game of a term system, and identifies the two-layer labelled
dependency graph of a term system with that occurrence game
(`labelledDependencyWinningMax_eq_winningMax`).

This module closes the remaining gap.  Every finite labelled digraph is
encoded as a term system with one occurrence per constraint vertex, of arity
the number of graph in-neighbours.  Graph strategies and occurrence
strategies translate into each other with literally the same winning
assignments, so the finite optimum of the graph game equals the optimum of
the encoding system.  The numerical statements of Proposition 5.5 and
Theorem 5.6 then transfer verbatim to arbitrary finite labelled digraphs,
and Corollary 6.3's exponent is shown to equal the guessing number of the
labelled dependency graph in the graph-game sense.

Author: Claude (Fable 5), verification pass of 27 August 2026.
-/

namespace TermCoding

universe uLabel uVertex uAlpha uSym uVar

namespace LabelledDigraph

variable {Label : Type uLabel}

section Finiteness

variable (G : LabelledDigraph.{uLabel, uVertex} Label) [Fintype G.Vertex]

noncomputable instance constraintVertexFintype :
    Fintype (ConstraintVertex G) := by
  classical
  change Fintype {v : G.Vertex // ¬ G.source v}
  letI : Finite {v : G.Vertex // ¬ G.source v} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

noncomputable instance inNeighbourFintype (v : G.Vertex) :
    Fintype (InNeighbour G v) := by
  classical
  change Fintype {u : G.Vertex // G.edge u v}
  letI : Finite {u : G.Vertex // G.edge u v} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

noncomputable instance strategyFintype {A : Type uAlpha} [Fintype A] :
    Fintype (Strategy G A) := by
  classical
  exact Fintype.ofFinite _

/-- Finite optimum of the labelled guessing game on `G` with alphabet `A`
(the paper's `W_n(G, λ, S)` for `A = Fin n`). -/
noncomputable def winningMax (A : Type uAlpha) [Fintype A] : Nat :=
  (Finset.univ : Finset (Strategy G A)).sup (winningCount G)

/-- Normalised guessing rate `log W_n / log n` of the labelled graph game. -/
noncomputable def winningRate (n : Nat) : Real :=
  Real.log (winningMax G (Fin n)) / Real.log n

/-- The guessing number `gn(G, λ, S)` of the labelled graph game, defined as
the supremum of the finite rates (shown below to be their limit). -/
noncomputable def winningRateSup : Real :=
  sSup {x : Real | ∃ n : Nat, 2 ≤ n ∧ x = winningRate G n}

end Finiteness

section Encoding

variable (G : LabelledDigraph.{uLabel, uVertex} Label) [Fintype G.Vertex]

/-- An enumeration of the constraint vertices. -/
noncomputable def constraintEquiv :
    ConstraintVertex G ≃ Fin (Fintype.card (ConstraintVertex G)) :=
  Fintype.equivFin _

/-- An enumeration of the in-neighbours of one vertex. -/
noncomputable def inNeighbourEquiv (v : G.Vertex) :
    InNeighbour G v ≃ Fin (Fintype.card (InNeighbour G v)) :=
  Fintype.equivFin _

/-- The number of occurrences of the encoding term system: one per
constraint vertex. -/
noncomputable abbrev occurrenceCount : Nat := Fintype.card (ConstraintVertex G)

/-- The constraint vertex behind occurrence `i`. -/
noncomputable abbrev vertexOf (i : Fin (occurrenceCount G)) :
    ConstraintVertex G :=
  (constraintEquiv G).symm i

/-- One function symbol per constraint vertex, of arity the number of graph
in-neighbours of that vertex. -/
noncomputable def signature : Signature.{uVertex} where
  Symbol := ConstraintVertex G
  arity := fun v => Fintype.card (InNeighbour G v.1)

/-- The encoding term system: occurrence `i` reads the labels of the
in-neighbours of its constraint vertex (in the enumeration order) and outputs
the label of that vertex. -/
noncomputable def termSystem :
    TermSystem (signature G) Label (occurrenceCount G) :=
  fun i =>
    { symbol := vertexOf G i
      args := fun p => G.label ((inNeighbourEquiv G (vertexOf G i).1).symm p).1
      output := G.label (vertexOf G i).1 }

variable {G}

/-- A graph strategy read as an occurrence strategy of the encoding system. -/
noncomputable def toOccurrence {A : Type uAlpha} (g : Strategy G A) :
    TermSystem.OccurrenceStrategy (A := A) (termSystem G) :=
  fun i input =>
    g (vertexOf G i) (fun u => input (inNeighbourEquiv G (vertexOf G i).1 u))

/-- Transport of an in-neighbour along an equality of vertices. -/
def transportIn {v w : G.Vertex} (h : v = w) (u : InNeighbour G v) :
    InNeighbour G w :=
  ⟨u.1, h ▸ u.2⟩

theorem vertexOf_constraintEquiv (v : ConstraintVertex G) :
    vertexOf G (constraintEquiv G v) = v :=
  (constraintEquiv G).symm_apply_apply v

/-- An occurrence strategy of the encoding system read as a graph
strategy. -/
noncomputable def ofOccurrence {A : Type uAlpha}
    (h : TermSystem.OccurrenceStrategy (A := A) (termSystem G)) :
    Strategy G A :=
  fun v input =>
    h (constraintEquiv G v)
      (fun p => input (transportIn
        (congrArg Subtype.val (vertexOf_constraintEquiv v))
        ((inNeighbourEquiv G (vertexOf G (constraintEquiv G v)).1).symm p)))

/-- The occurrence strategy `toOccurrence g` wins on exactly the assignments
on which `g` wins. -/
theorem wins_toOccurrence_iff {A : Type uAlpha} (g : Strategy G A)
    (a : Label → A) :
    TermSystem.Wins (termSystem G) (toOccurrence g) a ↔ G.Wins g a := by
  have key : ∀ i : Fin (occurrenceCount G),
      (toOccurrence g i (fun p => a ((termSystem G i).args p)) =
          a ((termSystem G i).output)) ↔
        (g (vertexOf G i) (fun u => a (G.label u.1)) =
          a (G.label (vertexOf G i).1)) := by
    intro i
    simp only [toOccurrence, termSystem, Equiv.symm_apply_apply]
  unfold TermSystem.Wins Wins
  rw [forall_congr' key]
  exact (Equiv.forall_congr_left
    (p := fun v : ConstraintVertex G =>
      g v (fun u => a (G.label u.1)) = a (G.label v.1))
    (constraintEquiv G)).symm

/-- The graph strategy `ofOccurrence h` wins on exactly the assignments on
which `h` wins. -/
theorem wins_ofOccurrence_iff {A : Type uAlpha}
    (h : TermSystem.OccurrenceStrategy (A := A) (termSystem G))
    (a : Label → A) :
    G.Wins (ofOccurrence h) a ↔ TermSystem.Wins (termSystem G) h a := by
  unfold Wins TermSystem.Wins
  refine Equiv.forall_congr (constraintEquiv G) (fun v => ?_)
  have hv : a (G.label (vertexOf G (constraintEquiv G v)).1) =
      a (G.label v.1) := by
    rw [vertexOf_constraintEquiv]
  simp only [ofOccurrence, termSystem, transportIn]
  rw [hv]

theorem winningCount_toOccurrence {A : Type uAlpha} (g : Strategy G A) :
    TermSystem.winningCount (termSystem G) (toOccurrence g) =
      G.winningCount g := by
  unfold TermSystem.winningCount winningCount
  exact Nat.card_congr
    (Equiv.subtypeEquivRight (fun a => wins_toOccurrence_iff g a))

theorem winningCount_ofOccurrence {A : Type uAlpha}
    (h : TermSystem.OccurrenceStrategy (A := A) (termSystem G)) :
    G.winningCount (ofOccurrence h) =
      TermSystem.winningCount (termSystem G) h := by
  unfold TermSystem.winningCount winningCount
  exact Nat.card_congr
    (Equiv.subtypeEquivRight (fun a => wins_ofOccurrence_iff h a))

variable (G)

/-- The finite optimum of the graph game equals the finite optimum of the
occurrence game of the encoding term system. -/
theorem winningMax_eq_termSystem [Fintype Label] (A : Type uAlpha)
    [Fintype A] :
    winningMax G A = TermSystem.winningMax (A := A) (termSystem G) := by
  classical
  apply Nat.le_antisymm
  · unfold winningMax
    apply Finset.sup_le
    intro g _
    rw [← winningCount_toOccurrence g]
    exact TermSystem.winningCount_le_winningMax _ _
  · unfold TermSystem.winningMax
    apply Finset.sup_le
    intro h _
    rw [← winningCount_ofOccurrence h]
    unfold winningMax
    exact Finset.le_sup (s := Finset.univ) (f := winningCount G)
      (Finset.mem_univ _)

end Encoding

section Numerical

variable (G : LabelledDigraph.{uLabel, uVertex} Label) [Fintype G.Vertex]
  [Fintype Label]

theorem winningRate_eq_termSystem (n : Nat) :
    winningRate G n = TermSystem.winningRate (termSystem G) n := by
  unfold winningRate TermSystem.winningRate
  rw [winningMax_eq_termSystem]

theorem winningRateSup_eq_termSystem :
    winningRateSup G = TermSystem.winningRateSup (termSystem G) := by
  unfold winningRateSup TermSystem.winningRateSup TermSystem.winningRateSet
  simp only [winningRate_eq_termSystem]

/-- Proposition 5.5(a) for an arbitrary finite labelled digraph:
`W_n ≤ W_m` for `1 ≤ n ≤ m`. -/
theorem winningMax_fin_monotone {n m : Nat} (hn : 0 < n) (hnm : n ≤ m) :
    winningMax G (Fin n) ≤ winningMax G (Fin m) := by
  rw [winningMax_eq_termSystem, winningMax_eq_termSystem]
  exact TermSystem.winningMax_fin_monotone hn hnm _

/-- Proposition 5.5(b) for an arbitrary finite labelled digraph:
`W_n · W_m ≤ W_{nm}`. -/
theorem winningMax_fin_mul_le {n m : Nat} (hn : 0 < n) (hm : 0 < m) :
    winningMax G (Fin n) * winningMax G (Fin m) ≤
      winningMax G (Fin (n * m)) := by
  simp only [winningMax_eq_termSystem]
  exact TermSystem.winningMax_fin_mul_le hn hm _

/-- Trivial bounds `1 ≤ W_n(G) ≤ n^{|Label|}` (nonempty alphabet). -/
theorem one_le_winningMax (A : Type uAlpha) [Fintype A] [Nonempty A] :
    1 ≤ winningMax G A := by
  rw [winningMax_eq_termSystem]
  exact TermSystem.one_le_winningMax _

theorem winningMax_le_assignmentCount (A : Type uAlpha) [Fintype A] :
    winningMax G A ≤ Fintype.card A ^ Fintype.card Label := by
  rw [winningMax_eq_termSystem]
  exact TermSystem.winningMax_le_assignmentCount _

/-- Theorem 5.6 for an arbitrary finite labelled digraph: the guessing rate
converges, and its limit is the guessing number `winningRateSup G`. -/
theorem winningRate_tendsto :
    Filter.Tendsto (winningRate G) Filter.atTop (nhds (winningRateSup G)) := by
  have hfun : winningRate G = TermSystem.winningRate (termSystem G) :=
    funext (winningRate_eq_termSystem G)
  rw [hfun, winningRateSup_eq_termSystem]
  exact TermSystem.winningRate_tendsto _

end Numerical

section Ordinary

/-- Definition 5.1: an ordinary digraph with a source set is the labelled
digraph with the identity labelling. -/
def ofSources (V : Type uVertex) (edge : V → V → Prop) (source : V → Prop) :
    LabelledDigraph V where
  Vertex := V
  edge := edge
  source := source
  label := id
  label_surjective := Function.surjective_id

instance ofSourcesVertexFintype {V : Type uVertex} [Fintype V]
    (edge : V → V → Prop) (source : V → Prop) :
    Fintype (ofSources V edge source).Vertex :=
  inferInstanceAs (Fintype V)

/-- With the identity labelling, `Wins` is literally the ordinary guessing
condition: every non-source vertex guesses its own value from its
in-neighbours. -/
theorem ofSources_wins_iff {V : Type uVertex} {edge : V → V → Prop}
    {source : V → Prop} {A : Type uAlpha}
    (g : Strategy (ofSources V edge source) A) (a : V → A) :
    (ofSources V edge source).Wins g a ↔
      ∀ v : ConstraintVertex (ofSources V edge source),
        g v (fun u => a u.1) = a v.1 :=
  Iff.rfl

/-- Theorem 5.6 for ordinary guessing games with sources. -/
theorem ofSources_winningRate_tendsto {V : Type uVertex} [Fintype V]
    (edge : V → V → Prop) (source : V → Prop) :
    Filter.Tendsto (winningRate (ofSources V edge source)) Filter.atTop
      (nhds (winningRateSup (ofSources V edge source))) :=
  winningRate_tendsto _

end Ordinary

end LabelledDigraph

namespace TermSystem

variable {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}

noncomputable instance labelledDependencyVertexFintype [Fintype Var]
    (Γ : TermSystem σ Var m) :
    Fintype (labelledDependencyGraph Γ).Vertex :=
  inferInstanceAs (Fintype (DependencyVertex Var m))

/-- The graph-game optimum of the paper's labelled dependency graph equals
the occurrence-game optimum of the term system. -/
theorem labelledDigraphWinningMax_eq_winningMax [Fintype Var]
    {A : Type uAlpha} [Fintype A] (Γ : TermSystem σ Var m) :
    LabelledDigraph.winningMax (labelledDependencyGraph Γ) A =
      winningMax (A := A) Γ := by
  rw [← labelledDependencyWinningMax_eq_winningMax]
  unfold LabelledDigraph.winningMax labelledDependencyWinningMax
  congr 1

theorem labelledDigraphWinningRate_eq [Fintype Var]
    (Γ : TermSystem σ Var m) (n : Nat) :
    LabelledDigraph.winningRate (labelledDependencyGraph Γ) n =
      winningRate Γ n := by
  unfold LabelledDigraph.winningRate winningRate
  rw [labelledDigraphWinningMax_eq_winningMax]

theorem labelledDigraphWinningRateSup_eq [Fintype Var]
    (Γ : TermSystem σ Var m) :
    LabelledDigraph.winningRateSup (labelledDependencyGraph Γ) =
      winningRateSup Γ := by
  unfold LabelledDigraph.winningRateSup winningRateSup winningRateSet
  simp only [labelledDigraphWinningRate_eq]

end TermSystem

namespace TermTheory

variable {σ : Signature.{uSym}} {Original : Type uVar} {m : Nat}
  [Fintype σ.Symbol] [Fintype Original]

/-- Corollary 6.3: the exponent of a term theory is the guessing number (in
the graph-game sense) of the labelled dependency graph of its normal form. -/
theorem exponent_eq_labelledDependencyRateSup (Γ : TermTheory σ Original m) :
    exponent Γ =
      LabelledDigraph.winningRateSup
        (TermSystem.labelledDependencyGraph (Normalisation.system Γ)) := by
  unfold exponent
  rw [TermSystem.labelledDigraphWinningRateSup_eq]

/-- Theorem 6.2 with the graph-game optimum of the labelled dependency graph
on both sides. -/
theorem finiteSandwich_labelledDependency [Nonempty Original]
    (Γ : TermTheory σ Original m) {n : Nat}
    (hcard : Normalisation.variableCount Γ ≤ n) :
    LabelledDigraph.winningMax
        (TermSystem.labelledDependencyGraph (Normalisation.system Γ))
        (Fin (n / Normalisation.variableCount Γ)) ≤
      maxSolutionCount (A := Fin n) Γ ∧
    maxSolutionCount (A := Fin n) Γ ≤
      LabelledDigraph.winningMax
        (TermSystem.labelledDependencyGraph (Normalisation.system Γ))
        (Fin n) := by
  rw [TermSystem.labelledDigraphWinningMax_eq_winningMax,
    TermSystem.labelledDigraphWinningMax_eq_winningMax]
  exact finiteSandwich Γ hcard

/-- Corollary 6.3 in the graph-game form: `log_n S_n(Γ)` converges to the
guessing number of the labelled dependency graph of the normal form. -/
theorem maxSolutionRate_tendsto_labelledDependency [Nonempty Original]
    (Γ : TermTheory σ Original m) :
    Filter.Tendsto (maxSolutionRate Γ) Filter.atTop
      (nhds (LabelledDigraph.winningRateSup
        (TermSystem.labelledDependencyGraph (Normalisation.system Γ)))) := by
  rw [← exponent_eq_labelledDependencyRateSup]
  exact maxSolutionRate_tendsto Γ

end TermTheory

end TermCoding
