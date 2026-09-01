import TermCoding.Cardinality

namespace TermCoding

universe uSym uVar uSmall uLarge

/-- A symbol together with an ordered tuple of inputs for that symbol. -/
abbrev OperationQuery (σ : Signature.{uSym}) (X : Type uVar) :=
  (s : σ.Symbol) × (Fin (σ.arity s) → X)

namespace OperationQuery

/-- Apply a map to every input coordinate of an operation query. -/
def map {σ : Signature.{uSym}} {X : Type uVar} {Y : Type uSmall}
    (f : X → Y) (q : OperationQuery σ X) : OperationQuery σ Y :=
  ⟨q.1, fun p => f (q.2 p)⟩

end OperationQuery

namespace Equation

/-- The left-hand side of a normal-form equation, including its symbol and
ordered argument-variable tuple. -/
def leftSide {σ : Signature.{uSym}} {Var : Type uVar}
    (e : Equation σ Var) : OperationQuery σ Var :=
  ⟨e.symbol, e.args⟩

end Equation

namespace TermSystem

/-- The Term-DAG/no-collision hypothesis: different equation occurrences
have different symbol-and-ordered-argument left-hand sides. -/
def NoCollision {σ : Signature.{uSym}} {Var : Type uVar} {m : Nat}
    (Γ : TermSystem σ Var m) : Prop :=
  Function.Injective (fun i => (Γ i).leftSide)

/-- A small-alphabet input at one equation occurrence. -/
abbrev BlockInput {σ : Signature.{uSym}} {Var : Type uVar}
    (B : Type uSmall) {m : Nat} (Γ : TermSystem σ Var m) :=
  (i : Fin m) × (Fin (σ.arity (Γ i).symbol) → B)

/-- Turn an occurrence-specific small input into an original-signature query
on disjoint variable blocks inside the large alphabet. -/
def blockQuery {σ : Signature.{uSym}} {Var : Type uVar}
    {B : Type uSmall} {A : Type uLarge} {m : Nat}
    (Γ : TermSystem σ Var m) (encode : Var × B ↪ A) :
    BlockInput B Γ → OperationQuery σ A
  | ⟨i, input⟩ =>
      ⟨(Γ i).symbol, fun p => encode ⟨(Γ i).args p, input p⟩⟩

/-- Decoding an encoded block element recovers its variable label and small
alphabet value. -/
theorem invFun_encode {Var : Type uVar} {B : Type uSmall}
    {A : Type uLarge} [Nonempty Var] [Nonempty B]
    (encode : Var × B ↪ A) (x : Var × B) :
    Function.invFun encode (encode x) = x :=
  Function.leftInverse_invFun encode.injective x

/-- Mapping the partial inverse of the block embedding over a block query
recovers the occurrence's variable labels and small input values. -/
theorem map_invFun_blockQuery {σ : Signature.{uSym}} {Var : Type uVar}
    {B : Type uSmall} {A : Type uLarge} {m : Nat}
    [Nonempty Var] [Nonempty B] (Γ : TermSystem σ Var m)
    (encode : Var × B ↪ A) (x : BlockInput B Γ) :
    OperationQuery.map (Function.invFun encode) (blockQuery Γ encode x) =
      ⟨(Γ x.1).symbol, fun p => ((Γ x.1).args p, x.2 p)⟩ := by
  cases x with
  | mk i input =>
      simp only [OperationQuery.map, blockQuery]
      have hinput :
          (fun p => Function.invFun encode
            (encode ((Γ i).args p, input p))) =
            (fun p => ((Γ i).args p, input p)) := by
        funext p
        exact invFun_encode encode _
      exact Sigma.ext
        (x := (⟨(Γ i).symbol, fun p => Function.invFun encode
          (encode ((Γ i).args p, input p))⟩ : OperationQuery σ (Var × B)))
        (y := (⟨(Γ i).symbol, fun p => ((Γ i).args p, input p)⟩ :
          OperationQuery σ (Var × B))) rfl (heq_of_eq hinput)

/-- Under no-collision, the large-alphabet queries belonging to distinct
occurrence/input pairs are disjoint. -/
theorem blockQuery_injective {σ : Signature.{uSym}} {Var : Type uVar}
    {B : Type uSmall} {A : Type uLarge} {m : Nat}
    [Nonempty Var] [Nonempty B] (Γ : TermSystem σ Var m)
    (hΓ : NoCollision Γ) (encode : Var × B ↪ A) :
    Function.Injective (blockQuery Γ encode) := by
  intro x y hxy
  have hdecoded := congrArg (OperationQuery.map (Function.invFun encode)) hxy
  rw [map_invFun_blockQuery, map_invFun_blockQuery] at hdecoded
  have hleft : (Γ x.1).leftSide = (Γ y.1).leftSide := by
    have hlabels := congrArg (OperationQuery.map Prod.fst) hdecoded
    simpa only [OperationQuery.map, Equation.leftSide] using hlabels
  have hindex : x.1 = y.1 := hΓ hleft
  cases x with
  | mk i input =>
      cases y with
      | mk j input' =>
          simp only at hindex
          subst j
          have hargs :
              (fun p => ((Γ i).args p, input p)) =
                (fun p => ((Γ i).args p, input' p)) :=
            eq_of_heq (Sigma.ext_iff.mp hdecoded).2
          have hinput : input = input' := by
            funext p
            exact congrArg Prod.snd (congrFun hargs p)
          subst input'
          rfl

/-- Interpret each original symbol piecewise on the disjoint query blocks,
using the occurrence-specific diversified strategy there and an arbitrary
value elsewhere. -/
noncomputable def blockInterpretation {σ : Signature.{uSym}}
    {Var : Type uVar} {B : Type uSmall} {A : Type uLarge} {m : Nat}
    [Nonempty A] (Γ : TermSystem σ Var m) (encode : Var × B ↪ A)
    (g : OccurrenceStrategy (A := B) Γ) : Interpretation σ A := by
  classical
  exact fun s input =>
    if h : ∃ x : BlockInput B Γ,
        blockQuery Γ encode x = (⟨s, input⟩ : OperationQuery σ A) then
      let x := Classical.choose h
      encode ⟨(Γ x.1).output, g x.1 x.2⟩
    else
      Classical.choice inferInstance

/-- On every designated variable block, the piecewise original
interpretation agrees with the diversified occurrence strategy. -/
theorem blockInterpretation_on_query {σ : Signature.{uSym}}
    {Var : Type uVar} {B : Type uSmall} {A : Type uLarge} {m : Nat}
    [Nonempty Var] [Nonempty B] [Nonempty A]
    (Γ : TermSystem σ Var m) (hΓ : NoCollision Γ)
    (encode : Var × B ↪ A) (g : OccurrenceStrategy (A := B) Γ)
    (i : Fin m) (input : Fin (σ.arity (Γ i).symbol) → B) :
    blockInterpretation Γ encode g (Γ i).symbol
        (fun p => encode ⟨(Γ i).args p, input p⟩) =
      encode ⟨(Γ i).output, g i input⟩ := by
  classical
  simp only [blockInterpretation]
  split
  next h =>
    let x := Classical.choose h
    have hx : blockQuery Γ encode x = blockQuery Γ encode ⟨i, input⟩ :=
      Classical.choose_spec h
    have hxi : x = ⟨i, input⟩ := blockQuery_injective Γ hΓ encode hx
    exact congrArg
      (fun y : BlockInput B Γ =>
        encode ⟨(Γ y.1).output, g y.1 y.2⟩) hxi
  next h =>
    exact False.elim (h ⟨⟨i, input⟩, rfl⟩)

/-- Encode a small-alphabet assignment in the variable-labelled blocks of the
large alphabet. -/
def encodeAssignment {Var : Type uVar} {B : Type uSmall} {A : Type uLarge}
    (encode : Var × B ↪ A) (a : Assignment Var B) : Assignment Var A :=
  fun v => encode ⟨v, a v⟩

/-- Every winning small-alphabet assignment becomes a solution of the
original system under the block interpretation. -/
theorem encodeAssignment_holds {σ : Signature.{uSym}} {Var : Type uVar}
    {B : Type uSmall} {A : Type uLarge} {m : Nat}
    [Nonempty Var] [Nonempty B] [Nonempty A]
    (Γ : TermSystem σ Var m) (hΓ : NoCollision Γ)
    (encode : Var × B ↪ A) (g : OccurrenceStrategy (A := B) Γ)
    (a : Assignment Var B) (ha : Wins Γ g a) :
    Holds Γ (blockInterpretation Γ encode g) (encodeAssignment encode a) := by
  intro i
  change blockInterpretation Γ encode g (Γ i).symbol
      (fun p => encode ⟨(Γ i).args p, a ((Γ i).args p)⟩) =
    encode ⟨(Γ i).output, a (Γ i).output⟩
  rw [blockInterpretation_on_query Γ hΓ encode g i]
  exact congrArg (fun b => encode ⟨(Γ i).output, b⟩) (ha i)

/-- The injection from winning assignments into original-system solutions
realising the diversification lower bound. -/
def winningToBlockSolution {σ : Signature.{uSym}} {Var : Type uVar}
    {B : Type uSmall} {A : Type uLarge} {m : Nat}
    [Nonempty Var] [Nonempty B] [Nonempty A]
    (Γ : TermSystem σ Var m) (hΓ : NoCollision Γ)
    (encode : Var × B ↪ A) (g : OccurrenceStrategy (A := B) Γ) :
    {a : Assignment Var B // Wins Γ g a} →
      Solutions Γ (blockInterpretation Γ encode g) :=
  fun a =>
    ⟨encodeAssignment encode a.1,
      encodeAssignment_holds Γ hΓ encode g a.1 a.2⟩

/-- The block solution map is injective because the block encoder is. -/
theorem winningToBlockSolution_injective {σ : Signature.{uSym}}
    {Var : Type uVar} {B : Type uSmall} {A : Type uLarge} {m : Nat}
    [Nonempty Var] [Nonempty B] [Nonempty A]
    (Γ : TermSystem σ Var m) (hΓ : NoCollision Γ)
    (encode : Var × B ↪ A) (g : OccurrenceStrategy (A := B) Γ) :
    Function.Injective (winningToBlockSolution Γ hΓ encode g) := by
  intro a b hab
  apply Subtype.ext
  funext v
  have hv := congrArg
    (fun z : Solutions Γ (blockInterpretation Γ encode g) => z.1 v) hab
  exact congrArg Prod.snd (encode.injective hv)

/-- Fixed-strategy lower bound furnished by the disjoint block
interpretation. -/
theorem winningCount_le_blockSolutionCount {σ : Signature.{uSym}}
    {Var : Type uVar} {B : Type uSmall} {A : Type uLarge} {m : Nat}
    [Fintype Var] [Fintype B] [Fintype A]
    [Nonempty Var] [Nonempty B] [Nonempty A]
    (Γ : TermSystem σ Var m) (hΓ : NoCollision Γ)
    (encode : Var × B ↪ A) (g : OccurrenceStrategy (A := B) Γ) :
    winningCount Γ g ≤
      solutionCount Γ (blockInterpretation Γ encode g) := by
  letI : Finite (Solutions Γ (blockInterpretation Γ encode g)) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Nat.card_le_card_of_injective
    (winningToBlockSolution Γ hΓ encode g)
    (winningToBlockSolution_injective Γ hΓ encode g)

/-- Every fixed interpretation is bounded by the original-system maximum. -/
theorem solutionCount_le_maxSolutionCount {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uLarge} {m : Nat}
    [Fintype σ.Symbol] [Fintype Var] [Fintype A]
    (Γ : TermSystem σ Var m) (I : Interpretation σ A) :
    solutionCount Γ I ≤ maxSolutionCount (A := A) Γ := by
  classical
  exact Finset.le_sup (s := Finset.univ) (f := solutionCount Γ)
    (Finset.mem_univ I)

/-- The lower half of the finite sandwich, stated at its exact combinatorial
interface: one disjoint block per variable is supplied by an embedding
`Var × B ↪ A`. -/
theorem winningMax_le_maxSolutionCount_of_embedding
    {σ : Signature.{uSym}} {Var : Type uVar}
    {B : Type uSmall} {A : Type uLarge} {m : Nat}
    [Fintype σ.Symbol] [Fintype Var] [Fintype B] [Fintype A]
    [Nonempty Var] [Nonempty B] [Nonempty A]
    (Γ : TermSystem σ Var m) (hΓ : NoCollision Γ)
    (encode : Var × B ↪ A) :
    winningMax (A := B) Γ ≤ maxSolutionCount (A := A) Γ := by
  obtain ⟨g, hg⟩ := exists_winningCount_eq_winningMax (A := B) Γ
  rw [← hg]
  exact (winningCount_le_blockSolutionCount Γ hΓ encode g).trans
    (solutionCount_le_maxSolutionCount Γ (blockInterpretation Γ encode g))

end TermSystem

end TermCoding
