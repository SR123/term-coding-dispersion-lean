import TermCoding.Asymptotics

namespace TermCoding

namespace Examples.SDOSExponents

/-- One binary operation symbol; at the labelled-game stage every equation
occurrence receives its own local rule. -/
inductive BinarySymbol where
  | f
deriving DecidableEq, Fintype

def binarySignature : Signature where
  Symbol := BinarySymbol
  arity := fun _ => 2

def binaryEquation {Var : Type} (u v out : Var) :
    Equation binarySignature Var where
  symbol := .f
  args := ![u, v]
  output := out

/-- View the inputs of any equation over the constant-binary signature as a
plain two-tuple.  This removes the harmless dependent arity wrapper. -/
def binaryInput {Var A : Type} {e : Equation binarySignature Var}
    (input : Fin (binarySignature.arity e.symbol) → A) : Fin 2 → A :=
  fun p => input ⟨p.val, p.isLt⟩

inductive Var2 where
  | x | y | z | w
deriving DecidableEq, Fintype

/-- Flattened six-equation form of the two-free-variable SDOS presentation. -/
def system2 : TermSystem binarySignature Var2 6 := ![
  binaryEquation .x .y .z,
  binaryEquation .y .x .w,
  binaryEquation .z .y .x,
  binaryEquation .x .w .y,
  binaryEquation .z .w .x,
  binaryEquation .w .z .y
]

def position2 : Fin 6 → Fin 2 := ![0, 0, 0, 1, 0, 0]

def strategy2 {A : Type} : TermSystem.OccurrenceStrategy (A := A) system2 :=
  fun i input => binaryInput input (position2 i)

def free2 {A : Type} (a : Assignment Var2 A) : A × A :=
  (a .x, a .y)

def extend2 {A : Type} (u : A × A) : Assignment Var2 A
  | .x => u.1
  | .y => u.2
  | .z => u.1
  | .w => u.2

theorem extend2_wins {A : Type} (u : A × A) :
    TermSystem.Wins system2 strategy2 (extend2 u) := by
  intro i
  fin_cases i <;>
    simp [strategy2, binaryInput, position2, system2, binaryEquation, extend2]

def free2EquivWinning {A : Type} :
    TypeEquiv (A × A)
      {a : Assignment Var2 A // TermSystem.Wins system2 strategy2 a} where
  toFun u := ⟨extend2 u, extend2_wins u⟩
  invFun a := free2 a.1
  left_inv _ := rfl
  right_inv a := by
    apply Subtype.ext
    funext v
    cases v with
    | x => rfl
    | y => rfl
    | z =>
        have h := a.2 (0 : Fin 6)
        simpa [system2, strategy2, binaryInput, position2, binaryEquation,
          free2, extend2] using h
    | w =>
        have h := a.2 (1 : Fin 6)
        simpa [system2, strategy2, binaryInput, position2, binaryEquation,
          free2, extend2] using h

/-- Every winning assignment of the two-variable presentation is determined
by its two original variables. -/
def free2Embedding {A : Type}
    (g : TermSystem.OccurrenceStrategy (A := A) system2) :
    {a : Assignment Var2 A // TermSystem.Wins system2 g a} ↪ A × A where
  toFun a := free2 a.1
  inj' := by
    intro a b hab
    have hx : a.1 .x = b.1 .x := congrArg Prod.fst hab
    have hy : a.1 .y = b.1 .y := congrArg Prod.snd hab
    have output_eq (i : Fin 6)
        (hargs : ∀ p, a.1 ((system2 i).args p) =
          b.1 ((system2 i).args p)) :
        a.1 (system2 i).output = b.1 (system2 i).output := by
      calc
        a.1 (system2 i).output =
            g i (fun p => a.1 ((system2 i).args p)) := (a.2 i).symm
        _ = g i (fun p => b.1 ((system2 i).args p)) := by
          congr 1
          funext p
          exact hargs p
        _ = b.1 (system2 i).output := b.2 i
    have hz : a.1 .z = b.1 .z := by
      apply output_eq 0
      intro p
      fin_cases p <;> assumption
    have hw : a.1 .w = b.1 .w := by
      apply output_eq 1
      intro p
      fin_cases p <;> assumption
    apply Subtype.ext
    funext v
    cases v <;> assumption

theorem winningCount2_le {A : Type} [Finite A]
    (g : TermSystem.OccurrenceStrategy (A := A) system2) :
    TermSystem.winningCount system2 g ≤ Nat.card (A × A) :=
  Nat.card_le_card_of_injective (free2Embedding g) (free2Embedding g).injective

theorem winningCount_strategy2 {A : Type} :
    TermSystem.winningCount system2 (strategy2 (A := A)) = Nat.card (A × A) :=
  Nat.card_congr (free2EquivWinning (A := A)).toEquiv.symm

/-- The labelled winning maximum of the two-free-variable presentation is
exactly `|A|^2` for every finite alphabet. -/
theorem winningMax2_eq {A : Type} [Fintype A] :
    TermSystem.winningMax (A := A) system2 = Fintype.card A ^ 2 := by
  classical
  have hupper :
      TermSystem.winningMax (A := A) system2 ≤ Nat.card (A × A) := by
    apply Finset.sup_le
    intro g _
    exact winningCount2_le g
  have hlower :
      Nat.card (A × A) ≤ TermSystem.winningMax (A := A) system2 := by
    rw [← winningCount_strategy2]
    exact TermSystem.winningCount_le_winningMax system2 strategy2
  have heq := Nat.le_antisymm hupper hlower
  simpa [Nat.card_prod, Nat.card_eq_fintype_card, pow_two] using heq

inductive Var8 where
  | x1 | y1 | x2 | y2 | x3 | y3 | x4 | y4
  | z1 | z2 | z3 | w3 | z4 | w4
deriving DecidableEq, Fintype

def original8 : Fin 8 → Var8 :=
  ![.x1, .y1, .x2, .y2, .x3, .y3, .x4, .y4]

/-- Flattened ten-equation form of the eight-free-variable separated SDOS
presentation. -/
def system8 : TermSystem binarySignature Var8 10 := ![
  binaryEquation .x1 .y1 .z1,
  binaryEquation .z1 .y1 .x1,
  binaryEquation .y2 .x2 .z2,
  binaryEquation .x2 .z2 .y2,
  binaryEquation .x3 .y3 .z3,
  binaryEquation .y3 .x3 .w3,
  binaryEquation .z3 .w3 .x3,
  binaryEquation .y4 .x4 .z4,
  binaryEquation .x4 .y4 .w4,
  binaryEquation .z4 .w4 .y4
]

def position8 : Fin 10 → Fin 2 := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0]

def strategy8 {A : Type} : TermSystem.OccurrenceStrategy (A := A) system8 :=
  fun i input => binaryInput input (position8 i)

def free8 {A : Type} (a : Assignment Var8 A) : Fin 8 → A :=
  fun i => a (original8 i)

def extend8 {A : Type} (u : Fin 8 → A) : Assignment Var8 A
  | .x1 => u 0
  | .y1 => u 1
  | .x2 => u 2
  | .y2 => u 3
  | .x3 => u 4
  | .y3 => u 5
  | .x4 => u 6
  | .y4 => u 7
  | .z1 => u 0
  | .z2 => u 3
  | .z3 => u 4
  | .w3 => u 5
  | .z4 => u 7
  | .w4 => u 6

theorem extend8_wins {A : Type} (u : Fin 8 → A) :
    TermSystem.Wins system8 strategy8 (extend8 u) := by
  intro i
  fin_cases i <;>
    simp [strategy8, binaryInput, position8, system8, binaryEquation, extend8]

def free8EquivWinning {A : Type} :
    TypeEquiv (Fin 8 → A)
      {a : Assignment Var8 A // TermSystem.Wins system8 strategy8 a} where
  toFun u := ⟨extend8 u, extend8_wins u⟩
  invFun a := free8 a.1
  left_inv u := by
    funext i
    fin_cases i <;> rfl
  right_inv a := by
    apply Subtype.ext
    funext v
    cases v with
    | x1 => rfl
    | y1 => rfl
    | x2 => rfl
    | y2 => rfl
    | x3 => rfl
    | y3 => rfl
    | x4 => rfl
    | y4 => rfl
    | z1 =>
        simpa [system8, strategy8, binaryInput, position8, binaryEquation,
          free8, original8, extend8]
          using a.2 0
    | z2 =>
        simpa [system8, strategy8, binaryInput, position8, binaryEquation,
          free8, original8, extend8]
          using a.2 2
    | z3 =>
        simpa [system8, strategy8, binaryInput, position8, binaryEquation,
          free8, original8, extend8]
          using a.2 4
    | w3 =>
        simpa [system8, strategy8, binaryInput, position8, binaryEquation,
          free8, original8, extend8]
          using a.2 5
    | z4 =>
        simpa [system8, strategy8, binaryInput, position8, binaryEquation,
          free8, original8, extend8]
          using a.2 7
    | w4 =>
        simpa [system8, strategy8, binaryInput, position8, binaryEquation,
          free8, original8, extend8]
          using a.2 8

/-- Every winning assignment of the separated presentation is determined by
its eight original variables. -/
def free8Embedding {A : Type}
    (g : TermSystem.OccurrenceStrategy (A := A) system8) :
    {a : Assignment Var8 A // TermSystem.Wins system8 g a} ↪ (Fin 8 → A) where
  toFun a := free8 a.1
  inj' := by
    intro a b hab
    have horig (i : Fin 8) : a.1 (original8 i) = b.1 (original8 i) :=
      congrFun hab i
    have output_eq (i : Fin 10)
        (hargs : ∀ p, a.1 ((system8 i).args p) =
          b.1 ((system8 i).args p)) :
        a.1 (system8 i).output = b.1 (system8 i).output := by
      calc
        a.1 (system8 i).output =
            g i (fun p => a.1 ((system8 i).args p)) := (a.2 i).symm
        _ = g i (fun p => b.1 ((system8 i).args p)) := by
          congr 1
          funext p
          exact hargs p
        _ = b.1 (system8 i).output := b.2 i
    have hz1 : a.1 .z1 = b.1 .z1 := by
      apply output_eq 0
      intro p
      fin_cases p
      · exact horig 0
      · exact horig 1
    have hz2 : a.1 .z2 = b.1 .z2 := by
      apply output_eq 2
      intro p
      fin_cases p
      · exact horig 3
      · exact horig 2
    have hz3 : a.1 .z3 = b.1 .z3 := by
      apply output_eq 4
      intro p
      fin_cases p
      · exact horig 4
      · exact horig 5
    have hw3 : a.1 .w3 = b.1 .w3 := by
      apply output_eq 5
      intro p
      fin_cases p
      · exact horig 5
      · exact horig 4
    have hz4 : a.1 .z4 = b.1 .z4 := by
      apply output_eq 7
      intro p
      fin_cases p
      · exact horig 7
      · exact horig 6
    have hw4 : a.1 .w4 = b.1 .w4 := by
      apply output_eq 8
      intro p
      fin_cases p
      · exact horig 6
      · exact horig 7
    apply Subtype.ext
    funext v
    cases v with
    | x1 => exact horig 0
    | y1 => exact horig 1
    | x2 => exact horig 2
    | y2 => exact horig 3
    | x3 => exact horig 4
    | y3 => exact horig 5
    | x4 => exact horig 6
    | y4 => exact horig 7
    | z1 => exact hz1
    | z2 => exact hz2
    | z3 => exact hz3
    | w3 => exact hw3
    | z4 => exact hz4
    | w4 => exact hw4

theorem winningCount8_le {A : Type} [Finite A]
    (g : TermSystem.OccurrenceStrategy (A := A) system8) :
    TermSystem.winningCount system8 g ≤ Nat.card (Fin 8 → A) :=
  Nat.card_le_card_of_injective (free8Embedding g) (free8Embedding g).injective

theorem winningCount_strategy8 {A : Type} :
    TermSystem.winningCount system8 (strategy8 (A := A)) =
      Nat.card (Fin 8 → A) :=
  Nat.card_congr (free8EquivWinning (A := A)).toEquiv.symm

/-- The labelled winning maximum of the separated presentation is exactly
`|A|^8` for every finite alphabet. -/
theorem winningMax8_eq {A : Type} [Fintype A] :
    TermSystem.winningMax (A := A) system8 = Fintype.card A ^ 8 := by
  classical
  have hupper :
      TermSystem.winningMax (A := A) system8 ≤ Nat.card (Fin 8 → A) := by
    apply Finset.sup_le
    intro g _
    exact winningCount8_le g
  have hlower :
      Nat.card (Fin 8 → A) ≤ TermSystem.winningMax (A := A) system8 := by
    rw [← winningCount_strategy8]
    exact TermSystem.winningCount_le_winningMax system8 strategy8
  have heq := Nat.le_antisymm hupper hlower
  simpa [Nat.card_fun, Nat.card_eq_fintype_card] using heq

/-- Numerical regression theorem: the two labelled maxima have exponents two
and eight on every finite alphabet, so they cannot share an invariant
presentation-independent exponent. -/
theorem presentation_regression (n : Nat) :
    TermSystem.winningMax (A := Fin n) system2 = n ^ 2 ∧
      TermSystem.winningMax (A := Fin n) system8 = n ^ 8 := by
  simpa using And.intro
    (winningMax2_eq (A := Fin n)) (winningMax8_eq (A := Fin n))

theorem winningRate2_eq (n : Nat) (hn : 2 ≤ n) :
    TermSystem.winningRate system2 n = 2 := by
  have hlog : Real.log (n : Real) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  unfold TermSystem.winningRate
  rw [winningMax2_eq]
  simp only [Fintype.card_fin, Nat.cast_pow, Real.log_pow]
  field_simp
  norm_num

theorem winningRate8_eq (n : Nat) (hn : 2 ≤ n) :
    TermSystem.winningRate system8 n = 8 := by
  have hlog : Real.log (n : Real) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hn))
  unfold TermSystem.winningRate
  rw [winningMax8_eq]
  simp only [Fintype.card_fin, Nat.cast_pow, Real.log_pow]
  field_simp
  norm_num

/-- Formal exponent statement corresponding to Proposition 8.6. -/
theorem winningRateSup2_eq :
    TermSystem.winningRateSup system2 = 2 := by
  have hset : TermSystem.winningRateSet system2 = {2} := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact Set.mem_singleton_iff.mpr (winningRate2_eq n hn)
    · intro hx
      have hx' : x = 2 := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨2, le_rfl, (winningRate2_eq 2 le_rfl).symm⟩
  unfold TermSystem.winningRateSup
  rw [hset]
  simp

/-- Formal exponent statement corresponding to Proposition 8.6. -/
theorem winningRateSup8_eq :
    TermSystem.winningRateSup system8 = 8 := by
  have hset : TermSystem.winningRateSet system8 = {8} := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact Set.mem_singleton_iff.mpr (winningRate8_eq n hn)
    · intro hx
      have hx' : x = 8 := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨2, le_rfl, (winningRate8_eq 2 le_rfl).symm⟩
  unfold TermSystem.winningRateSup
  rw [hset]
  simp

end Examples.SDOSExponents

end TermCoding
