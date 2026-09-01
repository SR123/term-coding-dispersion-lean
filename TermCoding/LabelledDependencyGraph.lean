import TermCoding.NeighbourCardinality

namespace TermCoding

universe uLabel uVertex uAlpha uSym uVar

/-- A labelled directed graph with a distinguished source predicate.  The
surjective label map implements the paper's shared-value semantics. -/
structure LabelledDigraph (Label : Type uLabel) where
  Vertex : Type uVertex
  edge : Vertex → Vertex → Prop
  source : Vertex → Prop
  label : Vertex → Label
  label_surjective : Function.Surjective label

namespace LabelledDigraph

/-- Vertices at which a local guessing condition is imposed. -/
def ConstraintVertex (G : LabelledDigraph.{uLabel, uVertex} Label) :=
  {v : G.Vertex // ¬ G.source v}

/-- The graph-theoretic in-neighbour type of one vertex. -/
def InNeighbour (G : LabelledDigraph.{uLabel, uVertex} Label)
    (v : G.Vertex) :=
  {u : G.Vertex // G.edge u v}

/-- A local rule at every non-source vertex, with one input for each distinct
graph in-neighbour. -/
abbrev Strategy (G : LabelledDigraph.{uLabel, uVertex} Label)
    (A : Type uAlpha) :=
  (v : ConstraintVertex G) → (InNeighbour G v.1 → A) → A

/-- A labelled configuration assigns one value per label; all vertices with
that label share the value. -/
def Wins (G : LabelledDigraph.{uLabel, uVertex} Label)
    {A : Type uAlpha} (g : Strategy G A) (a : Label → A) : Prop :=
  ∀ v, g v (fun u => a (G.label u.1)) = a (G.label v.1)

/-- Winning count for a fixed labelled-graph strategy. -/
noncomputable def winningCount (G : LabelledDigraph.{uLabel, uVertex} Label)
    {A : Type uAlpha} (g : Strategy G A) : Nat :=
  Nat.card {a : Label → A // G.Wins g a}

end LabelledDigraph

namespace TermSystem

/-- The paper's two-layer vertex set: one source vertex for each term
variable and one constraint vertex for each equation occurrence. -/
inductive DependencyVertex (Var : Type uVar) (m : Nat) where
  | varVertex : Var → DependencyVertex Var m
  | eqVertex : Fin m → DependencyVertex Var m
deriving DecidableEq, Fintype

/-- Edges run only from variable vertices to equation vertices, and record
the distinct variables in that equation's ordered argument tuple. -/
def dependencyEdge {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}
    (Γ : TermSystem σ Var m) :
    DependencyVertex Var m → DependencyVertex Var m → Prop
  | .varVertex v, .eqVertex i => ∃ p, (Γ i).args p = v
  | _, _ => False

/-- Exactly the variable layer is designated as the source set. -/
def dependencySource {Var : Type uVar} {m : Nat} :
    DependencyVertex Var m → Prop
  | .varVertex _ => True
  | .eqVertex _ => False

/-- Variable vertices retain their variable label; an equation vertex is
labelled by the output variable of that equation. -/
def dependencyLabel {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}
    (Γ : TermSystem σ Var m) : DependencyVertex Var m → Var
  | .varVertex v => v
  | .eqVertex i => (Γ i).output

theorem dependencyLabel_surjective {σ : Signature.{uSym}}
    {Var : Type uVar} {m : Nat} (Γ : TermSystem σ Var m) :
    Function.Surjective (dependencyLabel Γ) := by
  intro v
  exact ⟨DependencyVertex.varVertex v, rfl⟩

/-- The exact two-layer labelled dependency graph of Definition 5.9 in the
manuscript. -/
def labelledDependencyGraph {σ : Signature.{uSym}}
    {Var : Type uVar} {m : Nat} (Γ : TermSystem σ Var m) :
    LabelledDigraph Var where
  Vertex := DependencyVertex Var m
  edge := dependencyEdge Γ
  source := dependencySource
  label := dependencyLabel Γ
  label_surjective := dependencyLabel_surjective Γ

/-- The non-source graph vertex corresponding to an equation occurrence. -/
def equationConstraint {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}
    (Γ : TermSystem σ Var m) (i : Fin m) :
    LabelledDigraph.ConstraintVertex (labelledDependencyGraph Γ) :=
  ⟨DependencyVertex.eqVertex i, by
    simp [labelledDependencyGraph, dependencySource]⟩

/-- Each term-system neighbour gives the corresponding variable-layer graph
in-neighbour. -/
def neighbourToGraphInNeighbour {σ : Signature.{uSym}}
    {Var : Type uVar} {m : Nat} (Γ : TermSystem σ Var m) (i : Fin m)
    (v : Neighbour Γ i) :
    LabelledDigraph.InNeighbour (labelledDependencyGraph Γ)
      (equationConstraint Γ i).1 :=
  ⟨DependencyVertex.varVertex v.1, by
    simpa [labelledDependencyGraph, dependencyEdge] using v.2⟩

/-- Every in-neighbour of an equation-layer vertex is uniquely a variable
layer vertex and hence a term-system neighbour. -/
def graphInNeighbourToNeighbour {σ : Signature.{uSym}}
    {Var : Type uVar} {m : Nat} (Γ : TermSystem σ Var m) (i : Fin m)
    (u : LabelledDigraph.InNeighbour (labelledDependencyGraph Γ)
      (equationConstraint Γ i).1) : Neighbour Γ i := by
  rcases u with ⟨u, hu⟩
  cases u with
  | varVertex v =>
      exact ⟨v, by
        simpa [labelledDependencyGraph, dependencyEdge] using hu⟩
  | eqVertex j =>
      simp [labelledDependencyGraph, dependencyEdge] at hu

theorem graphInNeighbourToNeighbour_neighbourToGraph {σ : Signature.{uSym}}
    {Var : Type uVar} {m : Nat} (Γ : TermSystem σ Var m) (i : Fin m)
    (v : Neighbour Γ i) :
    graphInNeighbourToNeighbour Γ i (neighbourToGraphInNeighbour Γ i v) = v := by
  apply Subtype.ext
  rfl

theorem neighbourToGraph_graphInNeighbour {σ : Signature.{uSym}}
    {Var : Type uVar} {m : Nat} (Γ : TermSystem σ Var m) (i : Fin m)
    (u : LabelledDigraph.InNeighbour (labelledDependencyGraph Γ)
      (equationConstraint Γ i).1) :
    neighbourToGraphInNeighbour Γ i (graphInNeighbourToNeighbour Γ i u) = u := by
  rcases u with ⟨u, hu⟩
  cases u with
  | varVertex v => rfl
  | eqVertex j =>
      simp [labelledDependencyGraph, dependencyEdge] at hu

theorem graphInNeighbour_label {σ : Signature.{uSym}}
    {Var : Type uVar} {m : Nat} (Γ : TermSystem σ Var m) (i : Fin m)
    (u : LabelledDigraph.InNeighbour (labelledDependencyGraph Γ)
      (equationConstraint Γ i).1) :
    (labelledDependencyGraph Γ).label u.1 =
      (graphInNeighbourToNeighbour Γ i u).1 := by
  rcases u with ⟨u, hu⟩
  cases u with
  | varVertex v => rfl
  | eqVertex j =>
      simp [labelledDependencyGraph, dependencyEdge] at hu

/-- Turn the paper's graph strategy into the neighbour-variable strategy used
by the existing semantic kernel. -/
def graphToNeighbourStrategy {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m)
    (g : LabelledDigraph.Strategy (labelledDependencyGraph Γ) A) :
    NeighbourStrategy (A := A) Γ :=
  fun i input => g (equationConstraint Γ i)
    (fun u => input (graphInNeighbourToNeighbour Γ i u))

/-- Turn a neighbour-variable strategy into a strategy on the explicit
two-layer graph. -/
def neighbourToGraphStrategy {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m)
    (h : NeighbourStrategy (A := A) Γ) :
    LabelledDigraph.Strategy (labelledDependencyGraph Γ) A := by
  intro v input
  rcases v with ⟨v, hv⟩
  cases v with
  | varVertex x =>
      exact False.elim (hv (by
        simp [labelledDependencyGraph, dependencySource]))
  | eqVertex i =>
      exact h i (fun n => input (neighbourToGraphInNeighbour Γ i n))

/-- The explicit graph strategy obtained from a neighbour strategy has
exactly the same winning assignments. -/
theorem labelledWins_neighbourToGraph_iff {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (h : NeighbourStrategy (A := A) Γ)
    (a : Assignment Var A) :
    (labelledDependencyGraph Γ).Wins (neighbourToGraphStrategy Γ h) a ↔
      NeighbourWins Γ h a := by
  constructor
  · intro hw i
    have hi := hw (equationConstraint Γ i)
    simpa [neighbourToGraphStrategy, labelledDependencyGraph,
      dependencyLabel, neighbourToGraphInNeighbour] using hi
  · intro hw v
    rcases v with ⟨v, hv⟩
    cases v with
    | varVertex x =>
        exact False.elim (hv (by
          simp [labelledDependencyGraph, dependencySource]))
    | eqVertex i =>
        simpa [neighbourToGraphStrategy, labelledDependencyGraph,
          dependencyLabel, neighbourToGraphInNeighbour] using hw i

/-- Conversely, reading an explicit graph strategy as a neighbour strategy
also preserves the winning predicate exactly. -/
theorem neighbourWins_graphToNeighbour_iff {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m)
    (g : LabelledDigraph.Strategy (labelledDependencyGraph Γ) A)
    (a : Assignment Var A) :
    NeighbourWins Γ (graphToNeighbourStrategy Γ g) a ↔
      (labelledDependencyGraph Γ).Wins g a := by
  constructor
  · intro hw v
    rcases v with ⟨v, hv⟩
    cases v with
    | varVertex x =>
        exact False.elim (hv (by
          simp [labelledDependencyGraph, dependencySource]))
    | eqVertex i =>
        have hconstraint :
            (⟨DependencyVertex.eqVertex i, hv⟩ :
              LabelledDigraph.ConstraintVertex
                (labelledDependencyGraph Γ)) = equationConstraint Γ i :=
          Subtype.ext rfl
        rw [hconstraint]
        have hi := hw i
        change g (equationConstraint Γ i)
          (fun u => a (graphInNeighbourToNeighbour Γ i u).1) =
            a (Γ i).output at hi
        change g (equationConstraint Γ i)
          (fun u => a ((labelledDependencyGraph Γ).label u.1)) =
            a (Γ i).output
        have hinputs :
            (fun u => a ((labelledDependencyGraph Γ).label u.1)) =
              (fun u => a (graphInNeighbourToNeighbour Γ i u).1) := by
          funext u
          exact congrArg a (graphInNeighbour_label Γ i u)
        rw [hinputs]
        exact hi
  · intro hw i
    have hi := hw (equationConstraint Γ i)
    change g (equationConstraint Γ i)
      (fun u => a ((labelledDependencyGraph Γ).label u.1)) =
        a (Γ i).output at hi
    change g (equationConstraint Γ i)
      (fun u => a (graphInNeighbourToNeighbour Γ i u).1) =
        a (Γ i).output
    have hinputs :
        (fun u => a ((labelledDependencyGraph Γ).label u.1)) =
          (fun u => a (graphInNeighbourToNeighbour Γ i u).1) := by
      funext u
      exact congrArg a (graphInNeighbour_label Γ i u)
    rw [← hinputs]
    exact hi

def labelledWinningEquivNeighbour {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m)
    (g : LabelledDigraph.Strategy (labelledDependencyGraph Γ) A) :
    TypeEquiv
      {a : Assignment Var A // (labelledDependencyGraph Γ).Wins g a}
      {a : Assignment Var A //
        NeighbourWins Γ (graphToNeighbourStrategy Γ g) a} where
  toFun a := ⟨a.1, (neighbourWins_graphToNeighbour_iff Γ g a.1).2 a.2⟩
  invFun a := ⟨a.1, (neighbourWins_graphToNeighbour_iff Γ g a.1).1 a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def neighbourWinningEquivLabelled {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (h : NeighbourStrategy (A := A) Γ) :
    TypeEquiv {a : Assignment Var A // NeighbourWins Γ h a}
      {a : Assignment Var A //
        (labelledDependencyGraph Γ).Wins (neighbourToGraphStrategy Γ h) a} where
  toFun a := ⟨a.1, (labelledWins_neighbourToGraph_iff Γ h a.1).2 a.2⟩
  invFun a := ⟨a.1, (labelledWins_neighbourToGraph_iff Γ h a.1).1 a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance labelledDependencyConstraintFintype
    {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat} [Fintype Var]
    (Γ : TermSystem σ Var m) :
    Fintype (LabelledDigraph.ConstraintVertex
      (labelledDependencyGraph Γ)) := by
  change Fintype
    {v : DependencyVertex Var m // ¬ dependencySource v}
  letI : Finite {v : DependencyVertex Var m // ¬ dependencySource v} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

noncomputable instance labelledDependencyInNeighbourFintype
    {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat} [Fintype Var]
    (Γ : TermSystem σ Var m)
    (v : (labelledDependencyGraph Γ).Vertex) :
    Fintype (LabelledDigraph.InNeighbour (labelledDependencyGraph Γ) v) := by
  change Fintype {u : DependencyVertex Var m // dependencyEdge Γ u v}
  letI : Finite {u : DependencyVertex Var m // dependencyEdge Γ u v} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

noncomputable instance labelledDependencyStrategyFintype
    {σ : Signature.{uSym}} {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    [Fintype Var] [Fintype A] (Γ : TermSystem σ Var m) :
    Fintype (LabelledDigraph.Strategy (labelledDependencyGraph Γ) A) := by
  classical
  letI := labelledDependencyConstraintFintype Γ
  letI (v : LabelledDigraph.ConstraintVertex
      (labelledDependencyGraph Γ)) :=
    labelledDependencyInNeighbourFintype Γ v.1
  exact Fintype.ofFinite _

/-- Finite optimum for the explicit two-layer labelled graph. -/
noncomputable def labelledDependencyWinningMax {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    [Fintype Var] [Fintype A] (Γ : TermSystem σ Var m) : Nat := by
  classical
  exact (Finset.univ : Finset
    (LabelledDigraph.Strategy (labelledDependencyGraph Γ) A)).sup
      (LabelledDigraph.winningCount (labelledDependencyGraph Γ))

/-- The paper's explicit two-layer graph has exactly the same optimum as the
neighbour-variable labelled game. -/
theorem labelledDependencyWinningMax_eq_neighbourWinningMax
    {σ : Signature.{uSym}} {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    [Fintype Var] [Fintype A] (Γ : TermSystem σ Var m) :
    labelledDependencyWinningMax (A := A) Γ =
      neighbourWinningMax (A := A) Γ := by
  classical
  apply Nat.le_antisymm
  · unfold labelledDependencyWinningMax
    apply Finset.sup_le
    intro g _
    change Nat.card
      {a : Assignment Var A // (labelledDependencyGraph Γ).Wins g a} ≤ _
    rw [Nat.card_congr (labelledWinningEquivNeighbour Γ g).toEquiv]
    exact Finset.le_sup (s := Finset.univ)
      (f := neighbourWinningCount Γ) (Finset.mem_univ _)
  · unfold neighbourWinningMax
    apply Finset.sup_le
    intro h _
    change Nat.card {a : Assignment Var A // NeighbourWins Γ h a} ≤ _
    rw [Nat.card_congr (neighbourWinningEquivLabelled Γ h).toEquiv]
    unfold labelledDependencyWinningMax
    exact Finset.le_sup (s := Finset.univ)
      (f := LabelledDigraph.winningCount (labelledDependencyGraph Γ))
      (Finset.mem_univ _)

/-- Combining the explicit graph correspondence with the ordered-position
bridge proves equality with the occurrence-sensitive optimum used by the
principal theorem. -/
theorem labelledDependencyWinningMax_eq_winningMax
    {σ : Signature.{uSym}} {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    [Fintype Var] [Fintype A] (Γ : TermSystem σ Var m) :
    labelledDependencyWinningMax (A := A) Γ = winningMax (A := A) Γ := by
  rw [labelledDependencyWinningMax_eq_neighbourWinningMax,
    ← winningMax_eq_neighbourWinningMax]

end TermSystem

end TermCoding
