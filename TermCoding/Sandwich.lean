import TermCoding.BlockEmbedding

namespace TermCoding

universe uSym

namespace TermSystem

/-- The canonical injection of `k` disjoint blocks of size `q` into an
alphabet of size `n`, whenever `k*q ≤ n`. -/
def finBlockEmbedding {k q n : Nat} (h : k * q ≤ n) :
    Fin k × Fin q ↪ Fin n :=
  finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb h)

/-- The same block embedding for an arbitrary finite variable type, using its
canonical noncomputable equivalence with `Fin (card Var)`. -/
noncomputable def fintypeBlockEmbedding {Var : Type*} [Fintype Var]
    {q n : Nat} (h : Fintype.card Var * q ≤ n) :
    Var × Fin q ↪ Fin n :=
  ((Fintype.equivFin Var).prodCongr (Equiv.refl (Fin q))).toEmbedding.trans
    (finBlockEmbedding h)

/-- Exact finite sandwich for a collision-free normal-form system on `k`
variables, stated for any small block size `q` fitting in the large alphabet.
This is the cardinal form immediately before the floor substitution. -/
theorem finiteSandwich_of_mul_le {σ : Signature.{uSym}}
    {k q n m : Nat} [Fintype σ.Symbol]
    (hk : 0 < k) (hq : 0 < q) (hn : 0 < n)
    (hfit : k * q ≤ n) (Γ : TermSystem σ (Fin k) m)
    (hΓ : NoCollision Γ) :
    winningMax (A := Fin q) Γ ≤ maxSolutionCount (A := Fin n) Γ ∧
      maxSolutionCount (A := Fin n) Γ ≤ winningMax (A := Fin n) Γ := by
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  letI : NeZero q := ⟨Nat.ne_of_gt hq⟩
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  constructor
  · exact winningMax_le_maxSolutionCount_of_embedding Γ hΓ
      (finBlockEmbedding hfit)
  · exact maxSolutionCount_le_winningMax Γ

/-- The paper's floor-form finite sandwich:
`W_{⌊n/k⌋} ≤ S_n(Γ) ≤ W_n` for `n ≥ k ≥ 1`. -/
theorem finiteSandwich_floor {σ : Signature.{uSym}}
    {k n m : Nat} [Fintype σ.Symbol]
    (hk : 0 < k) (hkn : k ≤ n) (Γ : TermSystem σ (Fin k) m)
    (hΓ : NoCollision Γ) :
    winningMax (A := Fin (n / k)) Γ ≤
        maxSolutionCount (A := Fin n) Γ ∧
      maxSolutionCount (A := Fin n) Γ ≤ winningMax (A := Fin n) Γ := by
  have hq : 0 < n / k := Nat.div_pos hkn hk
  have hn : 0 < n := hk.trans_le hkn
  exact finiteSandwich_of_mul_le hk hq hn (Nat.mul_div_le n k) Γ hΓ

/-- Floor-form finite sandwich for an arbitrary nonempty finite variable
type. This is the form used after canonical normalisation, whose quotient
variable type need not literally be `Fin k`. -/
theorem finiteSandwich_fintype {σ : Signature.{uSym}} {Var : Type*}
    {n m : Nat} [Fintype σ.Symbol] [Fintype Var] [Nonempty Var]
    (hcard : Fintype.card Var ≤ n) (Γ : TermSystem σ Var m)
    (hΓ : NoCollision Γ) :
    winningMax (A := Fin (n / Fintype.card Var)) Γ ≤
        maxSolutionCount (A := Fin n) Γ ∧
      maxSolutionCount (A := Fin n) Γ ≤ winningMax (A := Fin n) Γ := by
  have hk : 0 < Fintype.card Var := Fintype.card_pos
  have hq : 0 < n / Fintype.card Var := Nat.div_pos hcard hk
  have hn : 0 < n := hk.trans_le hcard
  letI : NeZero (n / Fintype.card Var) := ⟨Nat.ne_of_gt hq⟩
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  constructor
  · exact winningMax_le_maxSolutionCount_of_embedding Γ hΓ
      (fintypeBlockEmbedding (Nat.mul_div_le n (Fintype.card Var)))
  · exact maxSolutionCount_le_winningMax Γ

end TermSystem

end TermCoding
