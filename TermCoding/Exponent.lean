import TermCoding.Asymptotics
import TermCoding.FullSandwich

namespace TermCoding

universe uSym uVar

namespace TermTheory

/-- Normalized logarithmic maximum solution rate of an arbitrary finite term
theory at numerical alphabet size `n`. -/
noncomputable def maxSolutionRate {σ : Signature.{uSym}}
    {Original : Type uVar} {m : Nat} [Fintype σ.Symbol]
    [Fintype Original] (Γ : TermTheory σ Original m) (n : Nat) : Real :=
  Real.log (maxSolutionCount (A := Fin n) Γ) / Real.log n

/-- The exponent assigned to an arbitrary term theory by its canonical
collision-free normal form. -/
noncomputable def exponent {σ : Signature.{uSym}}
    {Original : Type uVar} {m : Nat} [Fintype σ.Symbol]
    [Fintype Original] (Γ : TermTheory σ Original m) : Real :=
  TermSystem.winningRateSup (Normalisation.system Γ)

/-- Above the normalization variable count and alphabet size two, the raw
solution rate is nonnegative. -/
theorem maxSolutionRate_nonneg {σ : Signature.{uSym}}
    {Original : Type uVar} {m n : Nat} [Fintype σ.Symbol]
    [Fintype Original] [Nonempty Original] (Γ : TermTheory σ Original m)
    (hcard : Normalisation.variableCount Γ ≤ n) (hn : 2 ≤ n) :
    0 ≤ maxSolutionRate Γ n := by
  let k := Normalisation.variableCount Γ
  have hk : 0 < k := by
    exact Fintype.card_pos
  have hq : 0 < n / k := Nat.div_pos hcard hk
  letI : NeZero (n / k) := ⟨Nat.ne_of_gt hq⟩
  have hs := finiteSandwich Γ hcard
  have hS : 1 ≤ maxSolutionCount (A := Fin n) Γ :=
    (TermSystem.one_le_winningMax (Normalisation.system Γ)).trans hs.1
  have hlogS : 0 ≤ Real.log (maxSolutionCount (A := Fin n) Γ) :=
    Real.log_nonneg (by exact_mod_cast hS)
  have hlogn : 0 < Real.log (n : Real) :=
    Real.log_pos (by exact_mod_cast hn)
  exact div_nonneg hlogS hlogn.le

/-- The upper half of the finite sandwich after taking logarithms. -/
theorem maxSolutionRate_le_winningRate {σ : Signature.{uSym}}
    {Original : Type uVar} {m n : Nat} [Fintype σ.Symbol]
    [Fintype Original] [Nonempty Original] (Γ : TermTheory σ Original m)
    (hcard : Normalisation.variableCount Γ ≤ n) (hn : 2 ≤ n) :
    maxSolutionRate Γ n ≤
      TermSystem.winningRate (Normalisation.system Γ) n := by
  let k := Normalisation.variableCount Γ
  have hk : 0 < k := by
    exact Fintype.card_pos
  have hq : 0 < n / k := Nat.div_pos hcard hk
  letI : NeZero (n / k) := ⟨Nat.ne_of_gt hq⟩
  letI : NeZero n := ⟨Nat.ne_of_gt (by omega : 0 < n)⟩
  have hs := finiteSandwich Γ hcard
  have hS : 0 < (maxSolutionCount (A := Fin n) Γ : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
      ((TermSystem.one_le_winningMax
        (Normalisation.system Γ)).trans hs.1))
  have hW : 0 <
      (TermSystem.winningMax (A := Fin n)
        (Normalisation.system Γ) : Real) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
      (TermSystem.one_le_winningMax (Normalisation.system Γ)))
  have hcast :
      (maxSolutionCount (A := Fin n) Γ : Real) ≤
        TermSystem.winningMax (A := Fin n)
          (Normalisation.system Γ) := by
    exact_mod_cast hs.2
  have hlog := Real.strictMonoOn_log.monotoneOn hS hW hcast
  have hlogn : 0 < Real.log (n : Real) :=
    Real.log_pos (by exact_mod_cast hn)
  exact (div_le_div_iff_of_pos_right hlogn).2 hlog

/-- The normalized logarithmic maximum solution count of the original term
theory converges to the guessing exponent of its canonical normal form. This
is the formal version of the paper's finite-sandwich exponent theorem. -/
theorem maxSolutionRate_tendsto {σ : Signature.{uSym}}
    {Original : Type uVar} {m : Nat} [Fintype σ.Symbol]
    [Fintype Original] [Nonempty Original] (Γ : TermTheory σ Original m) :
    Filter.Tendsto (maxSolutionRate Γ) Filter.atTop
      (nhds (exponent Γ)) := by
  let Ω := Normalisation.system Γ
  let k := Normalisation.variableCount Γ
  have hk : 0 < k := by
    exact Fintype.card_pos
  rw [tendsto_order]
  constructor
  · intro a ha
    obtain ⟨r, hr, har⟩ :=
      (lt_csSup_iff (TermSystem.winningRateSet_bddAbove Ω)
        (TermSystem.winningRateSet_nonempty Ω)).1 ha
    obtain ⟨q, hq, rfl⟩ := hr
    by_cases ha0 : a < 0
    · filter_upwards [Filter.eventually_ge_atTop (max k 2)] with n hn
      exact ha0.trans_le (maxSolutionRate_nonneg Γ
        ((le_max_left k 2).trans hn) ((le_max_right k 2).trans hn))
    · have ha_nonneg : 0 ≤ a := le_of_not_gt ha0
      have hgap :
          0 < TermSystem.winningRate Ω q - a := sub_pos.mpr har
      have hlogq : 0 < Real.log (q : Real) :=
        Real.log_pos (by exact_mod_cast hq)
      obtain ⟨T, hT⟩ := exists_nat_gt
        ((a * Real.log (k : Real) + a * Real.log (q : Real)) /
          ((TermSystem.winningRate Ω q - a) * Real.log (q : Real)))
      let U := T + 1
      have hU :
          (a * Real.log (k : Real) + a * Real.log (q : Real)) /
                ((TermSystem.winningRate Ω q - a) * Real.log (q : Real)) <
            (U : Real) := by
        exact hT.trans (by exact_mod_cast (Nat.lt_succ_self T))
      filter_upwards [Filter.eventually_ge_atTop (k * q ^ U)] with n hn
      have hqpos : 0 < q := by omega
      have hUpow : q ^ U ≤ n / k := by
        apply (Nat.le_div_iff_mul_le hk).2
        simpa only [mul_comm] using hn
      have hUpos : 0 < U := by simp [U]
      have hqpow_one : 1 ≤ q ^ U := one_le_pow₀ (by omega)
      have hkn : k ≤ n := by
        calc
          k = k * 1 := by simp
          _ ≤ k * q ^ U := Nat.mul_le_mul_left k hqpow_one
          _ ≤ n := hn
      have hn2 : 2 ≤ n := by
        calc
          2 ≤ q := hq
          _ ≤ q ^ U := by
            calc
              q = q ^ 1 := by simp
              _ ≤ q ^ U := Nat.pow_le_pow_right hqpos hUpos
          _ ≤ n / k := hUpow
          _ ≤ n := Nat.div_le_self n k
      let s := n / k
      let t := Nat.log q s
      have hUt : U ≤ t :=
        Nat.le_log_of_pow_le (by omega) hUpow
      have hqts : q ^ t ≤ s :=
        Nat.pow_log_le_self q (by omega)
      have hspos : 0 < s := Nat.div_pos hkn hk
      have hslt : s < q ^ (t + 1) :=
        Nat.lt_pow_succ_log_self (by omega) s
      have hnlt : n < k * q ^ (t + 1) := by
        exact (Nat.lt_mul_div_succ n hk).trans_le
          (Nat.mul_le_mul_left k (Nat.succ_le_iff.mpr hslt))
      have hrealU :
          (a * Real.log (k : Real) + a * Real.log (q : Real)) /
                ((TermSystem.winningRate Ω q - a) * Real.log (q : Real)) <
            (t : Real) :=
        hU.trans_le (by exact_mod_cast hUt)
      have hbudget :
          a * Real.log (k : Real) + a * Real.log (q : Real) <
            (t : Real) * (TermSystem.winningRate Ω q - a) *
              Real.log (q : Real) := by
        simpa only [mul_assoc] using
          (div_lt_iff₀ (mul_pos hgap hlogq)).1 hrealU
      have hrate :
          TermSystem.winningRate Ω q * Real.log (q : Real) =
            Real.log (TermSystem.winningMax (A := Fin q) Ω) := by
        unfold TermSystem.winningRate
        field_simp [ne_of_gt hlogq]
      have hlogBudget :
          a * (Real.log (k : Real) +
              (t + 1 : Nat) * Real.log (q : Real)) <
            (t : Real) *
              Real.log (TermSystem.winningMax (A := Fin q) Ω) := by
        calc
          a * (Real.log (k : Real) +
                (t + 1 : Nat) * Real.log (q : Real)) =
              (a * Real.log (k : Real) + a * Real.log (q : Real)) +
                (t : Real) * a * Real.log (q : Real) := by
                  push_cast
                  ring
          _ < ((t : Real) * (TermSystem.winningRate Ω q - a) *
                Real.log (q : Real)) +
                (t : Real) * a * Real.log (q : Real) := by
              simpa only [add_assoc, add_left_comm, add_comm] using
                add_lt_add_right hbudget
                  ((t : Real) * a * Real.log (q : Real))
          _ = (t : Real) *
                (TermSystem.winningRate Ω q * Real.log (q : Real)) := by
              ring
          _ = (t : Real) *
                Real.log (TermSystem.winningMax (A := Fin q) Ω) := by
              rw [hrate]
      have hnreal : (0 : Real) < n := by positivity
      have hkreal : (0 : Real) < k := by exact_mod_cast hk
      have hqpowreal : (0 : Real) < (q ^ (t + 1) : Nat) := by positivity
      have hlognlt :
          Real.log (n : Real) <
            Real.log (k : Real) +
              (t + 1 : Nat) * Real.log (q : Real) := by
        have hcastlt : (n : Real) < (k * q ^ (t + 1) : Nat) := by
          exact_mod_cast hnlt
        have hloglt := Real.strictMonoOn_log hnreal
          (by positivity : (0 : Real) < (k * q ^ (t + 1) : Nat)) hcastlt
        rw [Nat.cast_mul, Real.log_mul hkreal.ne' hqpowreal.ne',
          Nat.cast_pow, Real.log_pow] at hloglt
        exact hloglt
      have haLog :
          a * Real.log (n : Real) <
            (t : Real) *
              Real.log (TermSystem.winningMax (A := Fin q) Ω) :=
        (mul_le_mul_of_nonneg_left hlognlt.le ha_nonneg).trans_lt hlogBudget
      have hsand := finiteSandwich Γ hkn
      have hcount :
          TermSystem.winningMax (A := Fin q) Ω ^ t ≤
            maxSolutionCount (A := Fin n) Γ := by
        calc
          TermSystem.winningMax (A := Fin q) Ω ^ t ≤
              TermSystem.winningMax (A := Fin (q ^ t)) Ω :=
            TermSystem.winningMax_pow_le hqpos Ω t
          _ ≤ TermSystem.winningMax (A := Fin s) Ω :=
            TermSystem.winningMax_fin_monotone
              (Nat.pow_pos hqpos) hqts Ω
          _ ≤ maxSolutionCount (A := Fin n) Γ := by
            simpa only [s] using hsand.1
      letI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
      have hWq : 0 <
          (TermSystem.winningMax (A := Fin q) Ω : Real) := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
          (TermSystem.one_le_winningMax Ω))
      have hSp : 0 < (maxSolutionCount (A := Fin n) Γ : Real) := by
        have hpone : 1 ≤ TermSystem.winningMax (A := Fin q) Ω ^ t := by
          exact one_le_pow₀ (TermSystem.one_le_winningMax Ω)
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (hpone.trans hcount))
      have hcastCount :
          ((TermSystem.winningMax (A := Fin q) Ω ^ t : Nat) : Real) ≤
            (maxSolutionCount (A := Fin n) Γ : Real) := by
        exact_mod_cast hcount
      have hlogCount := Real.strictMonoOn_log.monotoneOn
        (by
          rw [Nat.cast_pow]
          exact pow_pos hWq t)
        hSp hcastCount
      rw [Nat.cast_pow, Real.log_pow] at hlogCount
      have hnum :
          a * Real.log (n : Real) <
            Real.log (maxSolutionCount (A := Fin n) Γ) :=
        haLog.trans_le hlogCount
      have hlogn : 0 < Real.log (n : Real) :=
        Real.log_pos (by exact_mod_cast hn2)
      exact (lt_div_iff₀ hlogn).2 hnum
  · intro a ha
    filter_upwards [Filter.eventually_ge_atTop (max k 2)] with n hn
    exact (maxSolutionRate_le_winningRate Γ
      ((le_max_left k 2).trans hn) ((le_max_right k 2).trans hn)).trans_lt
        ((TermSystem.winningRate_le_sup Ω
          ((le_max_right k 2).trans hn)).trans_lt ha)

end TermTheory

end TermCoding
