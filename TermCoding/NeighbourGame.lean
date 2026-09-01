import TermCoding.LabelledGame

namespace TermCoding

universe uSym uVar uAlpha

namespace TermSystem

/-- The variables occurring in the ordered argument tuple of equation
occurrence `i`. This is the in-neighbour set of the corresponding labelled
constraint vertex. -/
def Neighbour {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}
    (Γ : TermSystem σ Var m) (i : Fin m) :=
  {v : Var // ∃ p, (Γ i).args p = v}

/-- A neighbour strategy sees one value for each distinct argument variable,
rather than one value for each argument position. -/
abbrev NeighbourStrategy {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m) :=
  (i : Fin m) → (Neighbour Γ i → A) → A

/-- Winning in the labelled neighbour-variable game. -/
def NeighbourWins {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m)
    (h : NeighbourStrategy (A := A) Γ) (a : Assignment Var A) : Prop :=
  ∀ i, h i (fun v => a v.1) = a (Γ i).output

/-- Every ordered argument position determines an in-neighbour, retaining a
witness of that occurrence. -/
def positionNeighbour {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}
    (Γ : TermSystem σ Var m) (i : Fin m)
    (p : Fin (σ.arity (Γ i).symbol)) : Neighbour Γ i :=
  ⟨(Γ i).args p, ⟨p, rfl⟩⟩

/-- Restrict an occurrence strategy to the consistent tuples induced by one
value per distinct neighbour variable. -/
def collapseToNeighbourStrategy {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m)
    (g : OccurrenceStrategy (A := A) Γ) : NeighbourStrategy (A := A) Γ :=
  fun i input => g i (fun p => input (positionNeighbour Γ i p))

/-- Collapsing repeated positions to neighbour variables preserves the
winning predicate definitionally. -/
theorem neighbourWins_collapse_iff {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (g : OccurrenceStrategy (A := A) Γ)
    (a : Assignment Var A) :
    NeighbourWins Γ (collapseToNeighbourStrategy Γ g) a ↔ Wins Γ g a := by
  rfl

/-- Extend a neighbour strategy arbitrarily to inconsistent positional
tuples by selecting one witness position for each neighbour variable. -/
noncomputable def expandNeighbourStrategy {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (h : NeighbourStrategy (A := A) Γ) :
    OccurrenceStrategy (A := A) Γ :=
  fun i input => h i (fun v => input (Classical.choose v.2))

/-- On assignment-induced (hence consistent) positional tuples, expanding a
neighbour strategy preserves winning exactly. -/
theorem wins_expandNeighbour_iff {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (h : NeighbourStrategy (A := A) Γ)
    (a : Assignment Var A) :
    Wins Γ (expandNeighbourStrategy Γ h) a ↔ NeighbourWins Γ h a := by
  classical
  have hinputs : ∀ i,
      (fun v : Neighbour Γ i =>
        a ((Γ i).args (Classical.choose v.2))) =
      (fun v : Neighbour Γ i => a v.1) := by
    intro i
    funext v
    rw [Classical.choose_spec v.2]
  constructor
  · intro hw i
    have hwi := hw i
    change h i (fun v => a ((Γ i).args (Classical.choose v.2))) =
      a (Γ i).output at hwi
    rw [hinputs i] at hwi
    exact hwi
  · intro hw i
    change h i (fun v => a ((Γ i).args (Classical.choose v.2))) =
      a (Γ i).output
    rw [hinputs i]
    exact hw i

/-- Winning configurations for a positional strategy and its collapsed
neighbour strategy are exactly equivalent. -/
def winningEquivNeighbourCollapse {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (g : OccurrenceStrategy (A := A) Γ) :
    TypeEquiv {a : Assignment Var A // Wins Γ g a}
      {a : Assignment Var A //
        NeighbourWins Γ (collapseToNeighbourStrategy Γ g) a} where
  toFun a := ⟨a.1, (neighbourWins_collapse_iff Γ g a.1).2 a.2⟩
  invFun a := ⟨a.1, (neighbourWins_collapse_iff Γ g a.1).1 a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Winning configurations for a neighbour strategy and its positional
extension are exactly equivalent. -/
def winningEquivNeighbourExpand {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (h : NeighbourStrategy (A := A) Γ) :
    TypeEquiv {a : Assignment Var A // NeighbourWins Γ h a}
      {a : Assignment Var A // Wins Γ (expandNeighbourStrategy Γ h) a} where
  toFun a := ⟨a.1, (wins_expandNeighbour_iff Γ h a.1).2 a.2⟩
  invFun a := ⟨a.1, (wins_expandNeighbour_iff Γ h a.1).1 a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end TermSystem

end TermCoding
