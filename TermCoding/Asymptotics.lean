import TermCoding.Alphabet

namespace TermCoding

universe uSym uVar uAlpha

namespace TermSystem

/-- A constant local strategy. -/
def constantStrategy {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m) (a₀ : A) :
    OccurrenceStrategy (A := A) Γ :=
  fun _ _ => a₀

def constantAssignment {Var : Type uVar} {A : Type uAlpha}
    (a₀ : A) : Assignment Var A :=
  fun _ => a₀

theorem constant_wins {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} (Γ : TermSystem σ Var m) (a₀ : A) :
    Wins Γ (constantStrategy Γ a₀) (constantAssignment a₀) := by
  intro i
  rfl

/-- Every nonempty finite alphabet admits at least one winning
configuration. -/
theorem one_le_winningMax {σ : Signature.{uSym}} {Var : Type uVar}
    {A : Type uAlpha} {m : Nat} [Fintype Var] [Fintype A] [Nonempty A]
    (Γ : TermSystem σ Var m) : 1 ≤ winningMax (A := A) Γ := by
  let a₀ : A := Classical.choice inferInstance
  let g := constantStrategy Γ a₀
  have hnonempty : Nonempty {a : Assignment Var A // Wins Γ g a} :=
    ⟨⟨constantAssignment a₀, constant_wins Γ a₀⟩⟩
  letI : Nonempty {a : Assignment Var A // Wins Γ g a} := hnonempty
  letI : Finite {a : Assignment Var A // Wins Γ g a} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact (Nat.succ_le_iff.mpr Nat.card_pos).trans
    (winningCount_le_winningMax Γ g)

/-- A winning set is a subset of the full assignment space. -/
theorem winningCount_le_assignmentCount {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    [Fintype Var] [Fintype A] (Γ : TermSystem σ Var m)
    (g : OccurrenceStrategy (A := A) Γ) :
    winningCount Γ g ≤ Fintype.card A ^ Fintype.card Var := by
  letI : Finite (Assignment Var A) := inferInstance
  have hcard := Nat.card_le_card_of_injective
    (fun a : {a : Assignment Var A // Wins Γ g a} => a.1)
    Subtype.val_injective
  simpa only [winningCount, Nat.card_fun, Nat.card_eq_fintype_card] using hcard

/-- The optimal winning count is at most the total number of assignments. -/
theorem winningMax_le_assignmentCount {σ : Signature.{uSym}}
    {Var : Type uVar} {A : Type uAlpha} {m : Nat}
    [Fintype Var] [Fintype A] (Γ : TermSystem σ Var m) :
    winningMax (A := A) Γ ≤ Fintype.card A ^ Fintype.card Var := by
  classical
  apply Finset.sup_le
  intro g _
  exact winningCount_le_assignmentCount Γ g

/-- Normalized logarithmic winning rate at numerical alphabet size `n`. -/
noncomputable def winningRate {σ : Signature.{uSym}} {Var : Type uVar}
    {m : Nat} [Fintype Var] (Γ : TermSystem σ Var m) (n : Nat) : Real :=
  Real.log (winningMax (A := Fin n) Γ) / Real.log n

/-- Every rate at alphabet size at least two is nonnegative. -/
theorem winningRate_nonneg {σ : Signature.{uSym}} {Var : Type uVar}
    {m n : Nat} [Fintype Var] (Γ : TermSystem σ Var m) (hn : 2 ≤ n) :
    0 ≤ winningRate Γ n := by
  letI : NeZero n := ⟨Nat.ne_of_gt (by omega : 0 < n)⟩
  have hW : 1 ≤ winningMax (A := Fin n) Γ := one_le_winningMax Γ
  have hlogW : 0 ≤ Real.log (winningMax (A := Fin n) Γ) := by
    exact Real.log_nonneg (by exact_mod_cast hW)
  have hlogn : 0 < Real.log (n : Real) := by
    exact Real.log_pos (by exact_mod_cast hn)
  exact div_nonneg hlogW hlogn.le

/-- The normalized rate is bounded by the number of variables. -/
theorem winningRate_le_card {σ : Signature.{uSym}} {Var : Type uVar}
    {m n : Nat} [Fintype Var] (Γ : TermSystem σ Var m) (hn : 2 ≤ n) :
    winningRate Γ n ≤ Fintype.card Var := by
  letI : NeZero n := ⟨Nat.ne_of_gt (by omega : 0 < n)⟩
  have hW := winningMax_le_assignmentCount (A := Fin n) Γ
  have hW' : winningMax (A := Fin n) Γ ≤ n ^ Fintype.card Var := by
    simpa using hW
  have hWpos : 0 < (winningMax (A := Fin n) Γ : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_winningMax Γ))
  have hnpow : 0 < ((n ^ Fintype.card Var : Nat) : Real) := by positivity
  have hlog := Real.strictMonoOn_log.monotoneOn hWpos hnpow
    (by exact_mod_cast hW')
  have hlogn : 0 < Real.log (n : Real) := by
    exact Real.log_pos (by exact_mod_cast hn)
  rw [Nat.cast_pow, Real.log_pow] at hlog
  change Real.log (winningMax (A := Fin n) Γ) / Real.log n ≤
    (Fintype.card Var : Real)
  exact (div_le_iff₀ hlogn).2 (by simpa [mul_comm] using hlog)

/-- Set of all rates at alphabet sizes at least two. -/
def winningRateSet {σ : Signature.{uSym}} {Var : Type uVar}
    {m : Nat} [Fintype Var] (Γ : TermSystem σ Var m) : Set Real :=
  {x | ∃ n, 2 ≤ n ∧ x = winningRate Γ n}

theorem winningRateSet_nonempty {σ : Signature.{uSym}} {Var : Type uVar}
    {m : Nat} [Fintype Var] (Γ : TermSystem σ Var m) :
    (winningRateSet Γ).Nonempty := by
  exact ⟨winningRate Γ 2, ⟨2, le_rfl, rfl⟩⟩

theorem winningRateSet_bddAbove {σ : Signature.{uSym}} {Var : Type uVar}
    {m : Nat} [Fintype Var] (Γ : TermSystem σ Var m) :
    BddAbove (winningRateSet Γ) := by
  refine ⟨Fintype.card Var, ?_⟩
  intro x hx
  obtain ⟨n, hn, rfl⟩ := hx
  exact winningRate_le_card Γ hn

/-- Supremal guessing rate. The convergence theorem below shows that this
supremum is a genuine limit. -/
noncomputable def winningRateSup {σ : Signature.{uSym}} {Var : Type uVar}
    {m : Nat} [Fintype Var] (Γ : TermSystem σ Var m) : Real :=
  sSup (winningRateSet Γ)

theorem winningRate_le_sup {σ : Signature.{uSym}} {Var : Type uVar}
    {m n : Nat} [Fintype Var] (Γ : TermSystem σ Var m) (hn : 2 ≤ n) :
    winningRate Γ n ≤ winningRateSup Γ := by
  exact le_csSup (winningRateSet_bddAbove Γ) ⟨n, hn, rfl⟩

/-- Iterated product lower bound at powers of a fixed alphabet size. -/
theorem winningMax_pow_le {σ : Signature.{uSym}} {Var : Type uVar}
    {m q : Nat} [Fintype Var] (hq : 0 < q) (Γ : TermSystem σ Var m)
    (t : Nat) :
    winningMax (A := Fin q) Γ ^ t ≤
      winningMax (A := Fin (q ^ t)) Γ := by
  induction t with
  | zero =>
      simp only [pow_zero]
      letI : NeZero (q ^ 0) := ⟨Nat.ne_of_gt (Nat.pow_pos hq)⟩
      exact one_le_winningMax Γ
  | succ t ih =>
      calc
        winningMax (A := Fin q) Γ ^ (t + 1) =
            winningMax (A := Fin q) Γ ^ t *
              winningMax (A := Fin q) Γ := by rw [pow_succ]
        _ ≤ winningMax (A := Fin (q ^ t)) Γ *
              winningMax (A := Fin q) Γ :=
          Nat.mul_le_mul_right _ ih
        _ ≤ winningMax (A := Fin (q ^ t * q)) Γ :=
          winningMax_fin_mul_le (Nat.pow_pos hq) hq Γ
        _ = winningMax (A := Fin (q ^ (t + 1))) Γ := by rw [pow_succ]

/-- The quantitative lower bound used in the convergence proof, before the
elementary floor-log ratio estimate. -/
theorem floorLog_logWinning_lower {σ : Signature.{uSym}}
    {Var : Type uVar} {m q n : Nat} [Fintype Var]
    (hq : 2 ≤ q) (hqn : q ≤ n) (Γ : TermSystem σ Var m) :
    ((Nat.log q n : Nat) : Real) *
          Real.log (winningMax (A := Fin q) Γ) / Real.log n ≤
      winningRate Γ n := by
  have hqpos : 0 < q := by omega
  have hnpos : 0 < n := lt_of_lt_of_le hqpos hqn
  let t := Nat.log q n
  have hpow : q ^ t ≤ n := Nat.pow_log_le_self q (Nat.ne_of_gt hnpos)
  have hpowerCount :
      winningMax (A := Fin q) Γ ^ t ≤ winningMax (A := Fin n) Γ :=
    (winningMax_pow_le hqpos Γ t).trans
      (winningMax_fin_monotone (Nat.pow_pos hqpos) hpow Γ)
  letI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
  letI : NeZero n := ⟨Nat.ne_of_gt hnpos⟩
  have hWq : 0 < (winningMax (A := Fin q) Γ : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_winningMax Γ))
  have hWn : 0 < (winningMax (A := Fin n) Γ : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_winningMax Γ))
  have hcast :
      ((winningMax (A := Fin q) Γ ^ t : Nat) : Real) ≤
        (winningMax (A := Fin n) Γ : Real) := by
    exact_mod_cast hpowerCount
  have hWqpow :
      0 < (((winningMax (A := Fin q) Γ ^ t : Nat) : Real)) := by
    rw [Nat.cast_pow]
    exact pow_pos hWq t
  have hlog :
      Real.log (((winningMax (A := Fin q) Γ ^ t : Nat) : Real)) ≤
        Real.log (winningMax (A := Fin n) Γ) :=
    Real.strictMonoOn_log.monotoneOn hWqpow hWn hcast
  rw [Nat.cast_pow, Real.log_pow] at hlog
  have hlogn : 0 < Real.log (n : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  change ((t : Nat) : Real) * Real.log (winningMax (A := Fin q) Γ) /
      Real.log n ≤
    Real.log (winningMax (A := Fin n) Γ) / Real.log n
  exact (div_le_div_iff_of_pos_right hlogn).2 hlog

/-- Paper-form floor-log estimate:
`rate n ≥ t/(t+1) * rate q`, where `t = floor(log_q n)`. -/
theorem floorLog_rate_lower {σ : Signature.{uSym}} {Var : Type uVar}
    {m q n : Nat} [Fintype Var]
    (hq : 2 ≤ q) (hqn : q ≤ n) (Γ : TermSystem σ Var m) :
    ((Nat.log q n : Nat) : Real) / (Nat.log q n + 1) *
        winningRate Γ q ≤ winningRate Γ n := by
  let t := Nat.log q n
  have hqpos : 0 < q := by omega
  have hnpos : 0 < n := lt_of_lt_of_le hqpos hqn
  have ht : 1 ≤ t := by
    exact Nat.le_log_of_pow_le (by omega) (by simpa using hqn)
  have hnlt : n < q ^ (t + 1) := by
    exact Nat.lt_pow_succ_log_self (by omega) n
  have hlogn : 0 < Real.log (n : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogq : 0 < Real.log (q : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < q by omega))
  have hcastlt : (n : Real) < ((q ^ (t + 1) : Nat) : Real) := by
    exact_mod_cast hnlt
  have hncastpos : 0 < (n : Real) := by positivity
  have hqpowcastpos : 0 < (((q ^ (t + 1) : Nat) : Real)) := by positivity
  have hloglt := Real.strictMonoOn_log hncastpos hqpowcastpos hcastlt
  rw [Nat.cast_pow, Real.log_pow] at hloglt
  have hfactor :
      (t : Real) / (t + 1) ≤ (t : Real) * Real.log q / Real.log n := by
    apply (div_le_div_iff₀ (by positivity : (0 : Real) < t + 1) hlogn).2
    have ht0 : (0 : Real) ≤ t := by positivity
    have hmul := mul_le_mul_of_nonneg_left hloglt.le ht0
    simpa only [Nat.cast_add, Nat.cast_one, mul_assoc, mul_left_comm,
      mul_comm] using hmul
  have hrateq : 0 ≤ winningRate Γ q := winningRate_nonneg Γ hq
  have hscaled := mul_le_mul_of_nonneg_right hfactor hrateq
  have hid :
      ((t : Real) * Real.log q / Real.log n) * winningRate Γ q =
        (t : Real) * Real.log (winningMax (A := Fin q) Γ) /
          Real.log n := by
    unfold winningRate
    field_simp [ne_of_gt hlogq, ne_of_gt hlogn]
  rw [hid] at hscaled
  exact hscaled.trans (floorLog_logWinning_lower hq hqn Γ)

/-- The supremal guessing rate is a genuine limit as the alphabet size tends
to infinity. This formalises Theorem 5.4's product-based convergence proof. -/
theorem winningRate_tendsto {σ : Signature.{uSym}} {Var : Type uVar}
    {m : Nat} [Fintype Var] (Γ : TermSystem σ Var m) :
    Filter.Tendsto (winningRate Γ) Filter.atTop
      (nhds (winningRateSup Γ)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨r, hr, har⟩ :=
      (lt_csSup_iff (winningRateSet_bddAbove Γ)
        (winningRateSet_nonempty Γ)).1 ha
    obtain ⟨q, hq, rfl⟩ := hr
    by_cases ha0 : a < 0
    · filter_upwards [Filter.eventually_ge_atTop (2 : Nat)] with n hn
      exact ha0.trans_le (winningRate_nonneg Γ hn)
    · have ha_nonneg : 0 ≤ a := le_of_not_gt ha0
      have hrpos : 0 < winningRate Γ q := ha_nonneg.trans_lt har
      have hgap : 0 < winningRate Γ q - a := sub_pos.mpr har
      obtain ⟨T, hT⟩ := exists_nat_gt
        (a / (winningRate Γ q - a))
      let U := T + 1
      have hU : a / (winningRate Γ q - a) < (U : Real) := by
        exact hT.trans (by
          exact_mod_cast (Nat.lt_succ_self T))
      filter_upwards [Filter.eventually_ge_atTop (q ^ U)] with n hn
      have hqpos : 0 < q := by omega
      have hqpow : q ≤ q ^ U := by
        calc
          q = q ^ 1 := by simp
          _ ≤ q ^ U := Nat.pow_le_pow_right hqpos (by simp [U])
      have hqn : q ≤ n := hqpow.trans hn
      have hUt : U ≤ Nat.log q n :=
        Nat.le_log_of_pow_le (by omega) hn
      have hreal :
          a / (winningRate Γ q - a) < (Nat.log q n : Real) :=
        hU.trans_le (by exact_mod_cast hUt)
      have hmul :
          a < (Nat.log q n : Real) * (winningRate Γ q - a) :=
        (div_lt_iff₀ hgap).1 hreal
      have htden : 0 < (Nat.log q n : Real) + 1 := by positivity
      have hfrac' :
          a < ((Nat.log q n : Real) * winningRate Γ q) /
            (Nat.log q n + 1) := by
        apply (lt_div_iff₀ htden).2
        nlinarith [hmul]
      have hfrac :
          a < ((Nat.log q n : Real) / (Nat.log q n + 1)) *
            winningRate Γ q := by
        simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hfrac'
      exact hfrac.trans_le (floorLog_rate_lower hq hqn Γ)
  · intro a ha
    filter_upwards [Filter.eventually_ge_atTop (2 : Nat)] with n hn
    exact (winningRate_le_sup Γ hn).trans_lt ha

end TermSystem

end TermCoding
