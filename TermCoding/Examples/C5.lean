import TermCoding.Asymptotics
import TermCoding.Examples.SDOSExponents

namespace TermCoding

namespace Examples.C5

open SDOSExponents

inductive Var where
  | v0 | v1 | v2 | v3 | v4
deriving DecidableEq, Fintype

def vertex : Fin 5 → Var := ![.v0, .v1, .v2, .v3, .v4]

/-- The bidirected five-cycle: every vertex is determined by its two cyclic
neighbours. -/
def system : TermSystem binarySignature Var 5 := ![
  binaryEquation .v4 .v1 .v0,
  binaryEquation .v0 .v2 .v1,
  binaryEquation .v1 .v3 .v2,
  binaryEquation .v2 .v4 .v3,
  binaryEquation .v3 .v0 .v4
]

/-- On a square alphabet `B × B`, guess `(second left, first right)`. -/
def pairStrategy {B : Type} :
    TermSystem.OccurrenceStrategy (A := B × B) system :=
  fun _ input =>
    ((binaryInput input 0).2, (binaryInput input 1).1)

/-- Five freely chosen coordinates generate the standard square-alphabet
winning configurations. -/
def cycleAssignment {B : Type} (u : Fin 5 → B) : Assignment Var (B × B)
  | .v0 => (u 0, u 1)
  | .v1 => (u 1, u 2)
  | .v2 => (u 2, u 3)
  | .v3 => (u 3, u 4)
  | .v4 => (u 4, u 0)

theorem cycleAssignment_wins {B : Type} (u : Fin 5 → B) :
    TermSystem.Wins system pairStrategy (cycleAssignment u) := by
  intro i
  fin_cases i <;>
    simp [system, pairStrategy, binaryInput, binaryEquation, cycleAssignment]

def cycleWinningEmbedding {B : Type} :
    (Fin 5 → B) ↪
      {a : Assignment Var (B × B) //
        TermSystem.Wins system pairStrategy a} where
  toFun u := ⟨cycleAssignment u, cycleAssignment_wins u⟩
  inj' := by
    intro u v huv
    funext i
    have hi := congrArg (fun a => (a.1 (vertex i)).1) huv
    fin_cases i <;> exact hi

/-- The explicit strategy has at least `|B|^5` winners. -/
theorem card_pow_five_le_winningCount {B : Type} [Fintype B] :
    Fintype.card B ^ 5 ≤
      TermSystem.winningCount system (pairStrategy (B := B)) := by
  letI : Finite
      {a : Assignment Var (B × B) //
        TermSystem.Wins system (pairStrategy (B := B)) a} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hcard := Nat.card_le_card_of_injective
    (cycleWinningEmbedding (B := B))
    (cycleWinningEmbedding (B := B)).injective
  simpa [Nat.card_fun, Nat.card_eq_fintype_card] using hcard

/-- Hence the optimal square-alphabet game also has at least `|B|^5`
winning configurations. -/
theorem card_pow_five_le_winningMax {B : Type} [Fintype B] :
    Fintype.card B ^ 5 ≤
      TermSystem.winningMax (A := B × B) system :=
  (card_pow_five_le_winningCount (B := B)).trans
    (TermSystem.winningCount_le_winningMax system (pairStrategy (B := B)))

theorem thirty_two_le_winningMax_four :
    32 ≤ TermSystem.winningMax (A := Fin 4) system := by
  have hlower := card_pow_five_le_winningMax (B := Fin 2)
  have hequiv := TermSystem.winningMax_eq_of_alphabetEquiv system
    (finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin (2 * 2))
  calc
    32 ≤ TermSystem.winningMax (A := Fin 2 × Fin 2) system := by
      norm_num at hlower ⊢
      exact hlower
    _ = TermSystem.winningMax (A := Fin 4) system := by
      simpa using hequiv

/-- The explicit square-alphabet construction gives the lower exponent
`5/2`.  A single alphabet of size four suffices because the winning-rate
limit is the supremum of all finite-alphabet rates. -/
theorem five_halves_le_winningRateSup :
    (5 : Real) / 2 ≤ TermSystem.winningRateSup system := by
  have hWnat := thirty_two_le_winningMax_four
  have hWpos : 0 <
      (TermSystem.winningMax (A := Fin 4) system : Real) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 32) hWnat)
  have hcast : (32 : Real) ≤
      TermSystem.winningMax (A := Fin 4) system := by
    exact_mod_cast hWnat
  have hlogW : Real.log (32 : Real) ≤
      Real.log (TermSystem.winningMax (A := Fin 4) system) :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hWpos hcast
  have hlog32 : Real.log (32 : Real) = 5 * Real.log (2 : Real) := by
    calc
      Real.log (32 : Real) = Real.log ((2 : Real) ^ 5) := by norm_num
      _ = 5 * Real.log (2 : Real) := Real.log_pow 2 5
  have hlog4 : Real.log (4 : Real) = 2 * Real.log (2 : Real) := by
    calc
      Real.log (4 : Real) = Real.log ((2 : Real) ^ 2) := by norm_num
      _ = 2 * Real.log (2 : Real) := Real.log_pow 2 2
  have hratio : (5 : Real) / 2 ≤ TermSystem.winningRate system 4 := by
    unfold TermSystem.winningRate
    rw [hlog32] at hlogW
    change (5 : Real) / 2 ≤
      Real.log (TermSystem.winningMax (A := Fin 4) system) /
        Real.log (4 : Real)
    rw [hlog4]
    have hden : 0 < (2 : Real) * Real.log (2 : Real) :=
      mul_pos (by norm_num) (Real.log_pos (by norm_num))
    apply (le_div_iff₀ hden).2
    nlinarith
  exact hratio.trans (TermSystem.winningRate_le_sup system (by norm_num))

/-- Linear certificate for the manuscript's `C₅` entropy upper bound.

The hypotheses name exactly the five functional-dependence equalities, six
submodularity instances, and four alphabet-size bounds used in the prose.
Once standard Shannon entropy supplies these hypotheses, Lean checks the
entire cancellation and coefficient argument. -/
theorem entropy_upper_linear_certificate
    (L H12345 H1234 H145 H14 H124 H234 H24 H12 H4 H1235 H345 H35
      H123 H125 H13 H2 H5 H25 : Real)
    (h145 : H145 = H14)
    (h234 : H234 = H24)
    (h345 : H345 = H35)
    (h123 : H123 = H13)
    (h125 : H125 = H25)
    (hsub1 : H14 + H12345 ≤ H1234 + H145)
    (hsub2 : H24 + H1234 ≤ H124 + H234)
    (hsub3 : H124 ≤ H12 + H4)
    (hsub4 : H35 + H12345 ≤ H1235 + H345)
    (hsub5 : H12 + H1235 ≤ H123 + H125)
    (hsub6 : H25 ≤ H2 + H5)
    (h13bound : H13 ≤ 2 * L)
    (h2bound : H2 ≤ L)
    (h4bound : H4 ≤ L)
    (h5bound : H5 ≤ L) :
    H12345 ≤ (5 : Real) / 2 * L := by
  linarith

/-- Once the standard entropy argument supplies the uniform upper bound on
every finite-alphabet winning rate, the formal lower construction and the
definition of the supremum give the exact `C₅` exponent. -/
theorem winningRateSup_eq_five_halves_of_upper
    (hupper : ∀ n, 2 ≤ n →
      TermSystem.winningRate system n ≤ (5 : Real) / 2) :
    TermSystem.winningRateSup system = (5 : Real) / 2 := by
  apply le_antisymm
  · unfold TermSystem.winningRateSup
    apply csSup_le (TermSystem.winningRateSet_nonempty system)
    intro r hr
    obtain ⟨n, hn, rfl⟩ := hr
    exact hupper n hn
  · exact five_halves_le_winningRateSup

end Examples.C5

end TermCoding
