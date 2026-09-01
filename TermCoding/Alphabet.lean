import TermCoding.Cardinality

namespace TermCoding

universe uSym uVar uSmall uLarge

namespace TermSystem

/-- Embed an assignment into a larger alphabet. -/
def embedAlphabetAssignment {Var : Type uVar} {A : Type uSmall}
    {B : Type uLarge} (e : A ↪ B) (a : Assignment Var A) :
    Assignment Var B :=
  fun v => e (a v)

/-- Extend a strategy from a nonempty subalphabet to a larger alphabet by
decoding inputs with `invFun`, applying the small strategy, and re-encoding
the output. On the embedded subalphabet this agrees exactly with the original
strategy; outside it the values are arbitrary. -/
noncomputable def extendAlphabetStrategy {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uSmall} {B : Type uLarge} {m : Nat}
    [Nonempty A] (Γ : TermSystem σ Var m) (e : A ↪ B)
    (g : OccurrenceStrategy (A := A) Γ) :
    OccurrenceStrategy (A := B) Γ :=
  fun i input => e (g i (fun p => Function.invFun e (input p)))

/-- Winning configurations remain winning after embedding the alphabet. -/
theorem embedAlphabetAssignment_wins {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uSmall} {B : Type uLarge} {m : Nat}
    [Nonempty A] (Γ : TermSystem σ Var m) (e : A ↪ B)
    (g : OccurrenceStrategy (A := A) Γ) (a : Assignment Var A)
    (ha : Wins Γ g a) :
    Wins Γ (extendAlphabetStrategy Γ e g) (embedAlphabetAssignment e a) := by
  intro i
  change e (g i (fun p => Function.invFun e (e (a ((Γ i).args p))))) =
    e (a (Γ i).output)
  have hinputs :
      (fun p => Function.invFun e (e (a ((Γ i).args p)))) =
        (fun p => a ((Γ i).args p)) := by
    funext p
    exact Function.leftInverse_invFun e.injective _
  rw [hinputs, ha i]

/-- Injection from small-alphabet winners to large-alphabet winners. -/
def winningAlphabetEmbeddingMap {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uSmall} {B : Type uLarge} {m : Nat}
    [Nonempty A] (Γ : TermSystem σ Var m) (e : A ↪ B)
    (g : OccurrenceStrategy (A := A) Γ) :
    {a : Assignment Var A // Wins Γ g a} →
      {b : Assignment Var B // Wins Γ (extendAlphabetStrategy Γ e g) b} :=
  fun a => ⟨embedAlphabetAssignment e a.1,
    embedAlphabetAssignment_wins Γ e g a.1 a.2⟩

theorem winningAlphabetEmbeddingMap_injective {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uSmall} {B : Type uLarge} {m : Nat}
    [Nonempty A] (Γ : TermSystem σ Var m) (e : A ↪ B)
    (g : OccurrenceStrategy (A := A) Γ) :
    Function.Injective (winningAlphabetEmbeddingMap Γ e g) := by
  intro a b hab
  apply Subtype.ext
  funext v
  exact e.injective (congrArg (fun z => z.1 v) hab)

/-- Fixed-strategy monotonicity under an alphabet embedding. -/
theorem winningCount_le_of_alphabetEmbedding {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uSmall} {B : Type uLarge} {m : Nat}
    [Fintype Var] [Fintype A] [Fintype B] [Nonempty A]
    (Γ : TermSystem σ Var m) (e : A ↪ B)
    (g : OccurrenceStrategy (A := A) Γ) :
    winningCount Γ g ≤ winningCount Γ (extendAlphabetStrategy Γ e g) := by
  letI : Finite
      {b : Assignment Var B // Wins Γ (extendAlphabetStrategy Γ e g) b} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Nat.card_le_card_of_injective
    (winningAlphabetEmbeddingMap Γ e g)
    (winningAlphabetEmbeddingMap_injective Γ e g)

/-- Optimal winning counts are monotone under alphabet embeddings. -/
theorem winningMax_le_of_alphabetEmbedding {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uSmall} {B : Type uLarge} {m : Nat}
    [Fintype Var] [Fintype A] [Fintype B] [Nonempty A]
    (Γ : TermSystem σ Var m) (e : A ↪ B) :
    winningMax (A := A) Γ ≤ winningMax (A := B) Γ := by
  obtain ⟨g, hg⟩ := exists_winningCount_eq_winningMax (A := A) Γ
  rw [← hg]
  exact (winningCount_le_of_alphabetEmbedding Γ e g).trans
    (winningCount_le_winningMax Γ (extendAlphabetStrategy Γ e g))

/-- The optimum depends only on alphabet cardinality, not on its concrete
type. -/
theorem winningMax_eq_of_alphabetEquiv {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uSmall} {B : Type uLarge} {m : Nat}
    [Fintype Var] [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (Γ : TermSystem σ Var m) (e : A ≃ B) :
    winningMax (A := A) Γ = winningMax (A := B) Γ := by
  apply Nat.le_antisymm
  · exact winningMax_le_of_alphabetEmbedding Γ e.toEmbedding
  · exact winningMax_le_of_alphabetEmbedding Γ e.symm.toEmbedding

/-- Numerical monotonicity `W_n ≤ W_m` for `1 ≤ n ≤ m`. -/
theorem winningMax_fin_monotone {σ : Signature.{uSym}} {Var : Type uVar}
    {n m r : Nat} [Fintype Var] (hn : 0 < n) (hnm : n ≤ m)
    (Γ : TermSystem σ Var r) :
    winningMax (A := Fin n) Γ ≤ winningMax (A := Fin m) Γ := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  exact winningMax_le_of_alphabetEmbedding Γ (Fin.castLEEmb hnm)

/-- Numerical product lower bound `W_n W_m ≤ W_{nm}`. -/
theorem winningMax_fin_mul_le {σ : Signature.{uSym}} {Var : Type uVar}
    {n m r : Nat} [Fintype Var] (hn : 0 < n) (hm : 0 < m)
    (Γ : TermSystem σ Var r) :
    winningMax (A := Fin n) Γ * winningMax (A := Fin m) Γ ≤
      winningMax (A := Fin (n * m)) Γ := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
  calc
    winningMax (A := Fin n) Γ * winningMax (A := Fin m) Γ ≤
        winningMax (A := Fin n × Fin m) Γ := winningMax_mul_le_product Γ
    _ = winningMax (A := Fin (n * m)) Γ :=
      winningMax_eq_of_alphabetEquiv Γ finProdFinEquiv

end TermSystem

end TermCoding
