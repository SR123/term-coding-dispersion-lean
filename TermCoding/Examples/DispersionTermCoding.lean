import TermCoding.FullSandwich
import TermCoding.Examples.Dispersion

set_option maxHeartbeats 1000000

namespace TermCoding

universe uSym uAlpha

namespace Examples.Dispersion

/-- Extend the original signature by one fresh `s`-ary decoder symbol for
each of the `k` input coordinates. -/
def codingSignature (σ : Signature.{uSym}) (k s : Nat) : Signature where
  Symbol := Sum σ.Symbol (Fin k)
  arity
    | Sum.inl f => σ.arity f
    | Sum.inr _ => s

noncomputable instance codingSignatureSymbolFintype
    {σ : Signature.{uSym}} {k s : Nat} [Fintype σ.Symbol] :
    Fintype (codingSignature σ k s).Symbol := by
  change Fintype (Sum σ.Symbol (Fin k))
  infer_instance

/-- Variables in the dispersion encoding: original input coordinates and
fresh output coordinates. -/
abbrev CodingVar (k s : Nat) := Sum (Fin k) (Fin s)

/-- Lift an original term into the enlarged signature and variable type. -/
def liftCodingTerm {σ : Signature.{uSym}} {k s : Nat} :
    Term σ (Fin k) → Term (codingSignature σ k s) (CodingVar k s)
  | .var v => .var (Sum.inl v)
  | .app f args =>
      .app (Sum.inl f) (fun p => liftCodingTerm (args p))

/-- The tuple-valued map induced by the displayed terms under one original
interpretation. -/
def termMap {σ : Signature.{uSym}} {A : Type uAlpha} {k s : Nat}
    (t : Fin s → Term σ (Fin k)) (I : Interpretation σ A) :
    Assignment (Fin k) A → Assignment (Fin s) A :=
  fun x i => (t i).eval I x

/-- The actual finite term theory from Proposition 9.2.  The first `s`
equations set fresh outputs equal to the terms; the next `k` equations apply
the fresh decoder symbols to recover each input coordinate. -/
def codingTheory {σ : Signature.{uSym}} {k s : Nat}
    (t : Fin s → Term σ (Fin k)) :
    TermTheory (codingSignature σ k s) (CodingVar k s) (s + k) :=
  Fin.addCases
    (fun i => {
      lhs := liftCodingTerm (t i)
      rhs := .var (Sum.inr i)
    })
    (fun j => {
      lhs := .app (Sum.inr j) (fun i => .var (Sum.inr i))
      rhs := .var (Sum.inl j)
    })

/-- Combine an input tuple and an output tuple into an assignment of the
enlarged term theory. -/
def codingAssignment {A : Type uAlpha} {k s : Nat}
    (x : Assignment (Fin k) A) (y : Assignment (Fin s) A) :
    Assignment (CodingVar k s) A :=
  Sum.elim x y

/-- Restrict an enlarged assignment to its input coordinates. -/
def codingInput {A : Type uAlpha} {k s : Nat}
    (a : Assignment (CodingVar k s) A) : Assignment (Fin k) A :=
  fun j => a (Sum.inl j)

/-- Restrict an enlarged assignment to its output coordinates. -/
def codingOutput {A : Type uAlpha} {k s : Nat}
    (a : Assignment (CodingVar k s) A) : Assignment (Fin s) A :=
  fun i => a (Sum.inr i)

/-- Extend an original interpretation by a freely chosen tuple-valued
decoder.  Decoder coordinate `j` interprets the fresh symbol `h_j`. -/
def extendCodingInterpretation {σ : Signature.{uSym}}
    {A : Type uAlpha} {k s : Nat} (I : Interpretation σ A)
    (h : Assignment (Fin s) A → Assignment (Fin k) A) :
    Interpretation (codingSignature σ k s) A
  | Sum.inl f => I f
  | Sum.inr j => fun y => h y j

/-- Restrict an enlarged interpretation to the original symbols. -/
def originalInterpretation {σ : Signature.{uSym}}
    {A : Type uAlpha} {k s : Nat}
    (J : Interpretation (codingSignature σ k s) A) :
    Interpretation σ A :=
  fun f => J (Sum.inl f)

/-- Read the fresh decoder symbols of an enlarged interpretation as one
tuple-valued decoder. -/
def decoderInterpretation {σ : Signature.{uSym}}
    {A : Type uAlpha} {k s : Nat}
    (J : Interpretation (codingSignature σ k s) A) :
    Assignment (Fin s) A → Assignment (Fin k) A :=
  fun y j => J (Sum.inr j) y

/-- Restricting and recombining an enlarged interpretation is exact. -/
theorem extend_restrictedCodingInterpretation {σ : Signature.{uSym}}
    {A : Type uAlpha} {k s : Nat}
    (J : Interpretation (codingSignature σ k s) A) :
    extendCodingInterpretation (originalInterpretation J)
      (decoderInterpretation J) = J := by
  funext z
  cases z <;> rfl

/-- Evaluation of a lifted term is evaluation of the original term on the
input restriction. -/
theorem liftCodingTerm_eval {σ : Signature.{uSym}}
    {A : Type uAlpha} {k s : Nat} (I : Interpretation σ A)
    (h : Assignment (Fin s) A → Assignment (Fin k) A)
    (a : Assignment (CodingVar k s) A) (u : Term σ (Fin k)) :
    (liftCodingTerm (s := s) u).eval
        (extendCodingInterpretation I h) a =
      u.eval I (codingInput a) := by
  induction u with
  | var v => rfl
  | app f args ih =>
      change
        I f (fun p => (liftCodingTerm (s := s) (args p)).eval
          (extendCodingInterpretation I h) a) =
        I f (fun p => (args p).eval I (codingInput a))
      congr 1
      funext p
      exact ih p

/-- Exact semantic reading of the syntactic dispersion theory: the fresh
outputs are the term map and the fresh decoders recover the input tuple. -/
theorem codingTheory_holds_iff {σ : Signature.{uSym}}
    {A : Type uAlpha} {k s : Nat}
    (t : Fin s → Term σ (Fin k)) (I : Interpretation σ A)
    (h : Assignment (Fin s) A → Assignment (Fin k) A)
    (a : Assignment (CodingVar k s) A) :
    (codingTheory t).Holds (extendCodingInterpretation I h) a ↔
      codingOutput a = termMap t I (codingInput a) ∧
        h (codingOutput a) = codingInput a := by
  constructor
  · intro hall
    constructor
    · funext i
      have hi := hall (Fin.castAdd k i)
      have hi' :
          (t i).eval I (codingInput a) = codingOutput a i := by
        simpa [codingTheory, TermEquation.Holds, liftCodingTerm_eval,
          codingOutput] using hi
      exact hi'.symm
    · funext j
      have hj := hall (Fin.natAdd s j)
      simpa [codingTheory, TermEquation.Holds, codingInput, codingOutput]
        using hj
  · rintro ⟨hout, hdecode⟩ q
    refine Fin.addCases ?_ ?_ q
    · intro i
      have hi := congrFun hout i
      simpa [codingTheory, TermEquation.Holds, liftCodingTerm_eval,
        codingOutput] using hi.symm
    · intro j
      have hj := congrFun hdecode j
      simpa [codingTheory, TermEquation.Holds, codingInput, codingOutput]
        using hj

/-- Exact fixed-interpretation equivalence between solutions of the displayed
term theory and the inputs selected by its tuple-valued decoder. -/
def codingSolutionsEquiv {σ : Signature.{uSym}}
    {A : Type uAlpha} {k s : Nat}
    (t : Fin s → Term σ (Fin k)) (I : Interpretation σ A)
    (h : Assignment (Fin s) A → Assignment (Fin k) A) :
    TypeEquiv
      (TermTheory.Solutions (codingTheory t)
        (extendCodingInterpretation I h))
      (DecoderSolutions (termMap t I) h) where
  toFun a := by
    refine ⟨codingInput a.1, ?_⟩
    have hs := (codingTheory_holds_iff t I h a.1).1 a.2
    rw [← hs.1]
    exact hs.2
  invFun x := by
    refine ⟨codingAssignment x.1 (termMap t I x.1), ?_⟩
    apply (codingTheory_holds_iff t I h _).2
    exact ⟨rfl, x.2⟩
  left_inv a := by
    apply Subtype.ext
    funext v
    cases v with
    | inl j => rfl
    | inr i =>
        have hs := (codingTheory_holds_iff t I h a.1).1 a.2
        exact (congrFun hs.1 i).symm
  right_inv x := by
    apply Subtype.ext
    rfl

/-- The same solution equivalence for an arbitrary interpretation of the
enlarged signature, obtained by reading off its original and decoder parts. -/
noncomputable def codingSolutionsEquivForInterpretation
    {σ : Signature.{uSym}} {A : Type uAlpha} {k s : Nat}
    (t : Fin s → Term σ (Fin k))
    (J : Interpretation (codingSignature σ k s) A) :
    TypeEquiv (TermTheory.Solutions (codingTheory t) J)
      (DecoderSolutions (termMap t (originalInterpretation J))
        (decoderInterpretation J)) := by
  rw [← extend_restrictedCodingInterpretation J]
  exact codingSolutionsEquiv t (originalInterpretation J)
    (decoderInterpretation J)

/-- Every fixed decoder is bounded by the finite decoder maximum. -/
theorem decoderSolutionCount_le_decoderMax {X : Type*} {Y : Type*}
    [Fintype X] [Fintype Y] (T : X → Y) (h : Y → X) :
    decoderSolutionCount T h ≤ decoderMax T := by
  classical
  unfold decoderMax
  exact Finset.le_sup (s := Finset.univ) (f := decoderSolutionCount T)
    (Finset.mem_univ h)

/-- The maximum solution count of the actual enlarged term theory is exactly
the nested maximum over original interpretations and freely chosen decoders. -/
theorem codingTheoryMax_eq_codedMax {σ : Signature.{uSym}}
    {A : Type uAlpha} {k s : Nat} [Fintype σ.Symbol] [Fintype A]
    (t : Fin s → Term σ (Fin k)) :
    TermTheory.maxSolutionCount (A := A) (codingTheory t) =
      codedMax (fun I : Interpretation σ A => termMap t I) := by
  classical
  unfold TermTheory.maxSolutionCount codedMax
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro J _
    let I := originalInterpretation J
    let h := decoderInterpretation J
    calc
      TermTheory.solutionCount (codingTheory t) J =
          decoderSolutionCount (termMap t I) h := by
        exact Nat.card_congr
          (codingSolutionsEquivForInterpretation t J).toEquiv
      _ ≤ decoderMax (termMap t I) := by
        exact decoderSolutionCount_le_decoderMax (termMap t I) h
      _ ≤ (Finset.univ : Finset (Interpretation σ A)).sup
          (fun I => decoderMax (termMap t I)) := by
        exact Finset.le_sup (s := Finset.univ)
          (f := fun I => decoderMax (termMap t I))
          (Finset.mem_univ I)
  · apply Finset.sup_le
    intro I _
    unfold decoderMax
    apply Finset.sup_le
    intro h _
    let J := extendCodingInterpretation I h
    calc
      decoderSolutionCount (termMap t I) h =
          TermTheory.solutionCount (codingTheory t) J := by
        exact Nat.card_congr (codingSolutionsEquiv t I h).toEquiv.symm
      _ ≤ (Finset.univ :
          Finset (Interpretation (codingSignature σ k s) A)).sup
          (TermTheory.solutionCount (codingTheory t)) := by
        exact Finset.le_sup (s := Finset.univ)
          (f := TermTheory.solutionCount (codingTheory t))
          (Finset.mem_univ J)

/-- Fully syntactic version of Proposition 9.2: after introducing the fresh
output variables and decoder symbols displayed in the paper, the ordinary
Term Coding optimum is exactly the dispersion optimum. -/
theorem codingTheoryMax_eq_dispersionMax {σ : Signature.{uSym}}
    {A : Type uAlpha} {k s : Nat} [Fintype σ.Symbol] [Fintype A]
    [Nonempty A] (t : Fin s → Term σ (Fin k)) :
    TermTheory.maxSolutionCount (A := A) (codingTheory t) =
      dispersionMax (fun I : Interpretation σ A => termMap t I) := by
  letI : Nonempty (Assignment (Fin k) A) :=
    ⟨fun _ => Classical.choice (inferInstance : Nonempty A)⟩
  rw [codingTheoryMax_eq_codedMax, codedMax_eq_dispersionMax]

end Examples.Dispersion

end TermCoding
