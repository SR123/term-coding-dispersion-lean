import TermCoding.Cardinality

namespace TermCoding

universe uX uY uTheta

namespace Examples.Dispersion

/-- The input points selected by a decoder `h` for a map `T`.  These are the
solutions of the section equations after the output variables have been
eliminated. -/
def DecoderSolutions {X : Type uX} {Y : Type uY}
    (T : X → Y) (h : Y → X) :=
  {x : X // h (T x) = x}

/-- The image of the term-defined map, as a finite type. -/
def ImagePoints {X : Type uX} {Y : Type uY} (T : X → Y) :=
  {y : Y // ∃ x, T x = y}

/-- A decoder solution maps injectively to its output value: applying the
decoder recovers the input. -/
def solutionsEmbeddingImage {X : Type uX} {Y : Type uY}
    (T : X → Y) (h : Y → X) :
    DecoderSolutions T h ↪ ImagePoints T where
  toFun x := ⟨T x.1, ⟨x.1, rfl⟩⟩
  inj' := by
    intro x x' hxx'
    apply Subtype.ext
    have hT : T x.1 = T x'.1 := congrArg Subtype.val hxx'
    calc
      x.1 = h (T x.1) := x.2.symm
      _ = h (T x'.1) := congrArg h hT
      _ = x'.1 := x'.2

/-- Every fixed decoder selects at most one input from each output fibre. -/
theorem decoderSolutions_card_le_image {X : Type uX} {Y : Type uY}
    [Finite X] [Finite Y] (T : X → Y) (h : Y → X) :
    Nat.card (DecoderSolutions T h) ≤ Nat.card (ImagePoints T) := by
  letI : Finite (ImagePoints T) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Nat.card_le_card_of_injective (solutionsEmbeddingImage T h)
    (solutionsEmbeddingImage T h).injective

/-- Choose one representative of every nonempty fibre, using an arbitrary
default only outside the image. -/
noncomputable def sectionDecoder {X : Type uX} {Y : Type uY} [Nonempty X]
    (T : X → Y) : Y → X := by
  classical
  intro y
  exact if hy : ∃ x, T x = y then Classical.choose hy
    else Classical.choice inferInstance

theorem sectionDecoder_spec {X : Type uX} {Y : Type uY} [Nonempty X]
    (T : X → Y) (y : Y) (hy : ∃ x, T x = y) :
    T (sectionDecoder T y) = y := by
  rw [sectionDecoder, dif_pos hy]
  exact Classical.choose_spec hy

/-- The chosen section gives an exact equivalence between output values in
the image and decoder solutions. -/
noncomputable def imageEquivSectionSolutions {X : Type uX} {Y : Type uY}
    [Nonempty X] (T : X → Y) :
    TypeEquiv (ImagePoints T) (DecoderSolutions T (sectionDecoder T)) where
  toFun y := by
    refine ⟨sectionDecoder T y.1, ?_⟩
    change sectionDecoder T (T (sectionDecoder T y.1)) = sectionDecoder T y.1
    rw [sectionDecoder_spec T y.1 y.2]
  invFun x := ⟨T x.1, ⟨x.1, rfl⟩⟩
  left_inv y := by
    apply Subtype.ext
    exact sectionDecoder_spec T y.1 y.2
  right_inv x := by
    apply Subtype.ext
    exact x.2

/-- Number of decoder solutions for one fixed decoder. -/
noncomputable def decoderSolutionCount {X : Type uX} {Y : Type uY}
    (T : X → Y) (h : Y → X) : Nat :=
  Nat.card (DecoderSolutions T h)

/-- Maximum number of section-equation solutions when the decoder may be
chosen freely. -/
noncomputable def decoderMax {X : Type uX} {Y : Type uY}
    [Fintype X] [Fintype Y] (T : X → Y) : Nat := by
  classical
  exact (Finset.univ : Finset (Y → X)).sup (decoderSolutionCount T)

/-- Formal core of Proposition 9.2: for each fixed term-defined map, the best
decoder selects exactly one representative of every nonempty fibre. -/
theorem decoderMax_eq_imageCard {X : Type uX} {Y : Type uY}
    [Fintype X] [Fintype Y] [Nonempty X] (T : X → Y) :
    decoderMax T = Nat.card (ImagePoints T) := by
  classical
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro h _
    exact decoderSolutions_card_le_image T h
  · have hsection :
        decoderSolutionCount T (sectionDecoder T) =
          Nat.card (ImagePoints T) := by
      exact Nat.card_congr (imageEquivSectionSolutions T).toEquiv.symm
    rw [← hsection]
    unfold decoderMax
    exact Finset.le_sup (s := Finset.univ) (f := decoderSolutionCount T)
      (Finset.mem_univ (sectionDecoder T))

/-- Dispersion after maximizing the image size over a finite family of
interpretations. -/
noncomputable def dispersionMax {Θ : Type uTheta} {X : Type uX}
    {Y : Type uY} [Fintype Θ] (T : Θ → X → Y) : Nat :=
  (Finset.univ : Finset Θ).sup (fun θ => Nat.card (ImagePoints (T θ)))

/-- Term-coding maximum after adjoining freely chosen decoder functions. -/
noncomputable def codedMax {Θ : Type uTheta} {X : Type uX}
    {Y : Type uY} [Fintype Θ] [Fintype X] [Fintype Y]
    (T : Θ → X → Y) : Nat :=
  (Finset.univ : Finset Θ).sup (fun θ => decoderMax (T θ))

/-- Maximizing also over the original interpretation preserves the exact
dispersion equality. -/
theorem codedMax_eq_dispersionMax {Θ : Type uTheta} {X : Type uX}
    {Y : Type uY} [Fintype Θ] [Fintype X] [Fintype Y] [Nonempty X]
    (T : Θ → X → Y) :
    codedMax T = dispersionMax T := by
  classical
  simp only [codedMax, dispersionMax, decoderMax_eq_imageCard]

end Examples.Dispersion

end TermCoding
