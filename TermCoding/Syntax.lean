namespace TermCoding

universe uSym uVar uAlpha uLeft uRight uThird

/-- A small dependency-free equivalence structure. Mathlib's `Equiv` can
replace this once the asymptotic layer introduces mathlib. -/
structure TypeEquiv (α : Type uLeft) (β : Type uRight) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

namespace TypeEquiv

/-- Composition for the dependency-light equivalence structure. -/
def trans {α : Type uLeft} {β : Type uRight} {γ : Type uThird}
    (e : TypeEquiv α β) (f : TypeEquiv β γ) : TypeEquiv α γ where
  toFun := fun a => f.toFun (e.toFun a)
  invFun := fun c => e.invFun (f.invFun c)
  left_inv a := by rw [f.left_inv, e.left_inv]
  right_inv c := by rw [e.right_inv, f.right_inv]

end TypeEquiv

/-- A single-sorted signature with an arity for every function symbol. -/
structure Signature where
  Symbol : Type uSym
  arity : Symbol → Nat

/-- A normal-form equation, retaining the ordered map from argument positions
to variables. Repeated variables are represented by a non-injective `args`. -/
structure Equation (σ : Signature.{uSym}) (Var : Type uVar) where
  symbol : σ.Symbol
  args : Fin (σ.arity symbol) → Var
  output : Var

/-- A finite system indexed by its equation occurrences. -/
abbrev TermSystem (σ : Signature.{uSym}) (Var : Type uVar) (m : Nat) :=
  Fin m → Equation σ Var

/-- An assignment of alphabet values to variables. -/
abbrev Assignment (Var : Type uVar) (A : Type uAlpha) := Var → A

/-- An interpretation supplies a total operation of the declared arity for
each symbol. -/
abbrev Interpretation (σ : Signature.{uSym}) (A : Type uAlpha) :=
  (s : σ.Symbol) → (Fin (σ.arity s) → A) → A

namespace Equation

/-- Satisfaction of one normal-form equation. -/
def Holds {σ : Signature.{uSym}} {Var : Type uVar} {A : Type uAlpha}
    (e : Equation σ Var) (I : Interpretation σ A) (a : Assignment Var A) : Prop :=
  I e.symbol (fun p => a (e.args p)) = a e.output

end Equation

namespace TermSystem

/-- Satisfaction of every indexed equation in a finite system. -/
def Holds {σ : Signature.{uSym}} {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (I : Interpretation σ A) (a : Assignment Var A) : Prop :=
  ∀ i, (Γ i).Holds I a

/-- The type of satisfying assignments for a fixed interpretation. -/
def Solutions {σ : Signature.{uSym}} {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    (Γ : TermSystem σ Var m) (I : Interpretation σ A) :=
  {a : Assignment Var A // Γ.Holds I a}

end TermSystem

end TermCoding
