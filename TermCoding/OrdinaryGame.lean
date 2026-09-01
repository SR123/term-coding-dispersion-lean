import Mathlib
import TermCoding.Cardinality

namespace TermCoding

universe uSym uVar uAlpha

namespace TermSystem

/-- A variable is defined when it is the output of at least one equation
occurrence.  The complementary variables are exactly the paper's sources. -/
def IsDefined {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}
    (Γ : TermSystem σ Var m) (v : Var) : Prop :=
  ∃ i, (Γ i).output = v

/-- The distinct in-neighbours of a variable in the paper's ordinary
dependency digraph: a variable is adjacent to the output when it occurs in
the ordered argument tuple of some equation defining that output. -/
def DependencyNeighbour {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}
    (Γ : TermSystem σ Var m) (v : Var) :=
  {u : Var // ∃ i, (Γ i).output = v ∧ ∃ p, (Γ i).args p = u}

/-- One ordinary local rule for each non-source (defined) variable. -/
abbrev OrdinaryStrategy {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m) :=
  (v : {v : Var // IsDefined Γ v}) →
    (DependencyNeighbour Γ v.1 → A) → A

/-- Winning in the ordinary variable-level dependency game. -/
def OrdinaryWins {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m)
    (g : OrdinaryStrategy (A := A) Γ) (a : Assignment Var A) : Prop :=
  ∀ v, g v (fun u => a u.1) = a v.1

/-- Functional normal form at the indexed equation level: no two distinct
equation occurrences define the same output variable. -/
def OutputFunctional {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}
    (Γ : TermSystem σ Var m) : Prop :=
  ∀ i j, (Γ i).output = (Γ j).output → i = j

/-- Choose one defining equation for every defined variable. -/
noncomputable def definingEquation {σ : Signature.{uSym}}
    {Var : Type uVar} {m : Nat} (Γ : TermSystem σ Var m)
    (v : {v : Var // IsDefined Γ v}) : Fin m :=
  Classical.choose v.2

@[simp] theorem definingEquation_output {σ : Signature.{uSym}}
    {Var : Type uVar} {m : Nat} (Γ : TermSystem σ Var m)
    (v : {v : Var // IsDefined Γ v}) :
    (Γ (definingEquation Γ v)).output = v.1 :=
  Classical.choose_spec v.2

/-- An argument position of the chosen equation is an in-neighbour of its
output in the ordinary dependency graph. -/
noncomputable def positionDependencyNeighbour {σ : Signature.{uSym}}
    {Var : Type uVar} {m : Nat} (Γ : TermSystem σ Var m)
    (v : {v : Var // IsDefined Γ v})
    (p : Fin (σ.arity (Γ (definingEquation Γ v)).symbol)) :
    DependencyNeighbour Γ v.1 :=
  ⟨(Γ (definingEquation Γ v)).args p,
    ⟨definingEquation Γ v, definingEquation_output Γ v, ⟨p, rfl⟩⟩⟩

/-- Choose one occurrence rule per output.  Every occurrence-winning
assignment remains winning in the resulting ordinary game; extra equations
can only make the occurrence game more restrictive. -/
noncomputable def occurrenceToOrdinaryStrategy {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (g : OccurrenceStrategy (A := A) Γ) :
    OrdinaryStrategy (A := A) Γ :=
  fun v input =>
    g (definingEquation Γ v)
      (fun p => input (positionDependencyNeighbour Γ v p))

theorem ordinaryWins_occurrenceToOrdinary_of_wins
    {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m)
    (g : OccurrenceStrategy (A := A) Γ) (a : Assignment Var A)
    (hw : Wins Γ g a) :
    OrdinaryWins Γ (occurrenceToOrdinaryStrategy Γ g) a := by
  intro v
  have hi := hw (definingEquation Γ v)
  simpa [occurrenceToOrdinaryStrategy] using hi

/-- Under functional normal form, every ordinary in-neighbour of an output
occurs in the unique equation defining that output. -/
theorem dependencyNeighbour_has_position_of_outputFunctional
    {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}
    (Γ : TermSystem σ Var m) (hfun : OutputFunctional Γ) (i : Fin m)
    (u : DependencyNeighbour Γ (Γ i).output) :
    ∃ p, (Γ i).args p = u.1 := by
  rcases u.2 with ⟨j, hj, p, hp⟩
  have hji : j = i := hfun j i hj
  subst j
  exact ⟨p, hp⟩

/-- Select a witnessing position for an ordinary in-neighbour when the
output has a unique defining equation. -/
noncomputable def dependencyNeighbourPosition
    {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}
    (Γ : TermSystem σ Var m) (hfun : OutputFunctional Γ) (i : Fin m)
    (u : DependencyNeighbour Γ (Γ i).output) :
    Fin (σ.arity (Γ i).symbol) :=
  Classical.choose
    (dependencyNeighbour_has_position_of_outputFunctional Γ hfun i u)

@[simp] theorem dependencyNeighbourPosition_spec
    {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}
    (Γ : TermSystem σ Var m) (hfun : OutputFunctional Γ) (i : Fin m)
    (u : DependencyNeighbour Γ (Γ i).output) :
    (Γ i).args (dependencyNeighbourPosition Γ hfun i u) = u.1 :=
  Classical.choose_spec
    (dependencyNeighbour_has_position_of_outputFunctional Γ hfun i u)

/-- In functional normal form, extend each ordinary local rule to the ordered
argument positions of the unique equation defining its output. -/
noncomputable def ordinaryToOccurrenceStrategy {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (hfun : OutputFunctional Γ)
    (h : OrdinaryStrategy (A := A) Γ) :
    OccurrenceStrategy (A := A) Γ :=
  fun i input =>
    h ⟨(Γ i).output, ⟨i, rfl⟩⟩
      (fun u => input (dependencyNeighbourPosition Γ hfun i u))

theorem wins_ordinaryToOccurrence_of_ordinaryWins
    {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m)
    (hfun : OutputFunctional Γ) (h : OrdinaryStrategy (A := A) Γ)
    (a : Assignment Var A) (hw : OrdinaryWins Γ h a) :
    Wins Γ (ordinaryToOccurrenceStrategy Γ hfun h) a := by
  intro i
  have hi := hw ⟨(Γ i).output, ⟨i, rfl⟩⟩
  change
    h ⟨(Γ i).output, ⟨i, rfl⟩⟩
        (fun u => a ((Γ i).args
          (dependencyNeighbourPosition Γ hfun i u))) =
      a (Γ i).output
  have hinput :
      (fun u : DependencyNeighbour Γ (Γ i).output =>
        a ((Γ i).args (dependencyNeighbourPosition Γ hfun i u))) =
      (fun u => a u.1) := by
    funext u
    rw [dependencyNeighbourPosition_spec]
  rw [hinput]
  exact hi

/-- The choose-one-definition translation gives an injection from every
occurrence-winning set into an ordinary-game winning set. -/
noncomputable def occurrenceWinningEmbeddingOrdinary
    {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m)
    (g : OccurrenceStrategy (A := A) Γ) :
    {a : Assignment Var A // Wins Γ g a} ↪
      {a : Assignment Var A //
        OrdinaryWins Γ (occurrenceToOrdinaryStrategy Γ g) a} where
  toFun a :=
    ⟨a.1, ordinaryWins_occurrenceToOrdinary_of_wins Γ g a.1 a.2⟩
  inj' := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z => z.1) hab

/-- Conversely, in functional normal form, an ordinary winning set injects
into the winning set of its positional extension. -/
noncomputable def ordinaryWinningEmbeddingOccurrence
    {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m)
    (hfun : OutputFunctional Γ) (h : OrdinaryStrategy (A := A) Γ) :
    {a : Assignment Var A // OrdinaryWins Γ h a} ↪
      {a : Assignment Var A //
        Wins Γ (ordinaryToOccurrenceStrategy Γ hfun h) a} where
  toFun a :=
    ⟨a.1, wins_ordinaryToOccurrence_of_ordinaryWins Γ hfun h a.1 a.2⟩
  inj' := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z => z.1) hab

noncomputable instance dependencyNeighbourFintype
    {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}
    [Fintype Var] (Γ : TermSystem σ Var m) (v : Var) :
    Fintype (DependencyNeighbour Γ v) := by
  letI : Finite (DependencyNeighbour Γ v) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

noncomputable instance ordinaryStrategyFintype
    {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} [Fintype Var] [Fintype A]
    (Γ : TermSystem σ Var m) :
    Fintype (OrdinaryStrategy (A := A) Γ) :=
  Fintype.ofFinite _

/-- The occurrence-diversified signature has the finite symbol type
`Fin m`, exposed as an instance for finite maximisation. -/
noncomputable instance diversifiedSignatureSymbolFintype
    {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}
    (Γ : TermSystem σ Var m) :
    Fintype (diversifiedSignature Γ).Symbol := by
  change Fintype (Fin m)
  infer_instance

/-- Winning count for one ordinary variable-level strategy. -/
noncomputable def ordinaryWinningCount {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (g : OrdinaryStrategy (A := A) Γ) : Nat :=
  Nat.card {a : Assignment Var A // OrdinaryWins Γ g a}

/-- The maximum winning count in the paper's ordinary dependency digraph. -/
noncomputable def ordinaryWinningMax {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    [Fintype Var] [Fintype A] (Γ : TermSystem σ Var m) : Nat :=
  (Finset.univ : Finset (OrdinaryStrategy (A := A) Γ)).sup
    (ordinaryWinningCount Γ)

theorem winningCount_le_ordinaryWinningCount
    {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} [Finite Var] [Finite A]
    (Γ : TermSystem σ Var m)
    (g : OccurrenceStrategy (A := A) Γ) :
    winningCount Γ g ≤
      ordinaryWinningCount Γ (occurrenceToOrdinaryStrategy Γ g) := by
  exact Nat.card_le_card_of_injective
    (occurrenceWinningEmbeddingOrdinary Γ g)
    (occurrenceWinningEmbeddingOrdinary Γ g).injective

theorem ordinaryWinningCount_le_winningCount_of_outputFunctional
    {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} [Finite Var] [Finite A]
    (Γ : TermSystem σ Var m)
    (hfun : OutputFunctional Γ) (h : OrdinaryStrategy (A := A) Γ) :
    ordinaryWinningCount Γ h ≤
      winningCount Γ (ordinaryToOccurrenceStrategy Γ hfun h) := by
  exact Nat.card_le_card_of_injective
    (ordinaryWinningEmbeddingOccurrence Γ hfun h)
    (ordinaryWinningEmbeddingOccurrence Γ hfun h).injective

/-- Formal counterpart of the manuscript's unlabelled upper bound: choosing
one defining equation per output can only enlarge the winning set. -/
theorem winningMax_le_ordinaryWinningMax
    {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} [Fintype Var] [Fintype A]
    (Γ : TermSystem σ Var m) :
    winningMax (A := A) Γ ≤ ordinaryWinningMax (A := A) Γ := by
  classical
  apply Finset.sup_le
  intro g _
  exact (winningCount_le_ordinaryWinningCount Γ g).trans
    (Finset.le_sup (s := Finset.univ)
      (f := ordinaryWinningCount Γ) (Finset.mem_univ _))

/-- In functional normal form, the occurrence/labelled optimum is exactly
the ordinary dependency-digraph optimum. -/
theorem winningMax_eq_ordinaryWinningMax_of_outputFunctional
    {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} [Fintype Var] [Fintype A]
    (Γ : TermSystem σ Var m) (hfun : OutputFunctional Γ) :
    winningMax (A := A) Γ = ordinaryWinningMax (A := A) Γ := by
  apply Nat.le_antisymm
  · exact winningMax_le_ordinaryWinningMax Γ
  · classical
    apply Finset.sup_le
    intro h _
    exact
      (ordinaryWinningCount_le_winningCount_of_outputFunctional Γ hfun h).trans
        (winningCount_le_winningMax Γ _)

/-- Maximising interpretations of the occurrence-diversified signature is
exactly the same finite optimisation as maximising occurrence strategies. -/
theorem diversifiedMaxSolutionCount_eq_winningMax
    {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} [Fintype Var] [Fintype A]
    (Γ : TermSystem σ Var m) :
    maxSolutionCount (A := A) (diversify Γ) =
      winningMax (A := A) Γ := by
  classical
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro I _
    have hcount :
        solutionCount (diversify Γ) I =
          winningCount Γ (interpretationToStrategy Γ I) := by
      unfold solutionCount winningCount
      exact
        (winningCard_eq_diversifiedSolutionCard Γ
          (interpretationToStrategy Γ I)).symm
    rw [hcount]
    exact winningCount_le_winningMax Γ _
  · apply Finset.sup_le
    intro g _
    have hcount :
        winningCount Γ g =
          solutionCount (diversify Γ) (strategyToInterpretation Γ g) := by
      unfold solutionCount winningCount
      exact winningCard_eq_diversifiedSolutionCard Γ g
    rw [hcount]
    exact Finset.le_sup (s := Finset.univ)
      (f := solutionCount (diversify Γ))
      (Finset.mem_univ (strategyToInterpretation Γ g))

/-- Exact finite form of the manuscript's functional diversified
instance/ordinary dependency-digraph correspondence. -/
theorem diversifiedMaxSolutionCount_eq_ordinaryWinningMax_of_outputFunctional
    {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} [Fintype Var] [Fintype A]
    (Γ : TermSystem σ Var m) (hfun : OutputFunctional Γ) :
    maxSolutionCount (A := A) (diversify Γ) =
      ordinaryWinningMax (A := A) Γ := by
  rw [diversifiedMaxSolutionCount_eq_winningMax,
    winningMax_eq_ordinaryWinningMax_of_outputFunctional Γ hfun]

/-- The original shared-symbol solution maximum is bounded by the ordinary
dependency-digraph game even without functional normal form. -/
theorem maxSolutionCount_le_ordinaryWinningMax
    {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat}
    [Fintype σ.Symbol] [Fintype Var] [Fintype A]
    (Γ : TermSystem σ Var m) :
    maxSolutionCount (A := A) Γ ≤ ordinaryWinningMax (A := A) Γ :=
  (maxSolutionCount_le_winningMax Γ).trans
    (winningMax_le_ordinaryWinningMax Γ)

end TermSystem

end TermCoding
