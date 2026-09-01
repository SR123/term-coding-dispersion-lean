import TermCoding.Examples.Dispersion

namespace TermCoding

universe u

namespace Examples.PartialSOLS

/-- The ordered superposition map associated with a binary operation. -/
def superposition {A : Type u} (f : A → A → A) (p : A × A) : A × A :=
  (f p.1 p.2, f p.2 p.1)

/-- Four decoder maps appearing in the standard SOLS presentation. -/
structure Decoders (A : Type u) where
  row : A → A → A
  column : A → A → A
  first : A → A → A
  second : A → A → A

/-- Satisfaction of the four standard SOLS equations at one ordered pair. -/
structure Holds {A : Type u} (f : A → A → A) (d : Decoders A)
    (p : A × A) : Prop where
  row_decode : d.row (f p.1 p.2) p.2 = p.1
  column_decode : d.column p.1 (f p.1 p.2) = p.2
  first_decode : d.first (f p.1 p.2) (f p.2 p.1) = p.1
  second_decode : d.second (f p.1 p.2) (f p.2 p.1) = p.2

/-- The type of ordered pairs satisfying all four equations. -/
def Solutions {A : Type u} (f : A → A → A) (d : Decoders A) :=
  {p : A × A // Holds f d p}

/-- Injectivity in each column of a partial Latin square. -/
def RowInjectiveOn {A : Type u} (C : A × A → Prop)
    (f : A → A → A) : Prop :=
  ∀ ⦃x x' y : A⦄, C (x, y) → C (x', y) →
    f x y = f x' y → x = x'

/-- Injectivity in each row of a partial Latin square. -/
def ColumnInjectiveOn {A : Type u} (C : A × A → Prop)
    (f : A → A → A) : Prop :=
  ∀ ⦃x y y' : A⦄, C (x, y) → C (x, y') →
    f x y = f x y' → y = y'

/-- Injectivity of the ordered superposition map on a partial code. -/
def SuperpositionInjectiveOn {A : Type u} (C : A × A → Prop)
    (f : A → A → A) : Prop :=
  ∀ ⦃p q : A × A⦄, C p → C q →
    superposition f p = superposition f q → p = q

/-- The first decoder forces injectivity in each fixed-second-coordinate
fibre of every solution code. -/
theorem rowInjectiveOn_of_holds {A : Type u} (C : A × A → Prop)
    (f : A → A → A) (d : Decoders A)
    (hholds : ∀ p, C p → Holds f d p) :
    RowInjectiveOn C f := by
  intro x x' y hxy hx'y heq
  have hx := hholds (x, y) hxy
  have hx' := hholds (x', y) hx'y
  calc
    x = d.row (f x y) y := hx.row_decode.symm
    _ = d.row (f x' y) y := congrArg (fun u => d.row u y) heq
    _ = x' := hx'.row_decode

/-- The second decoder forces injectivity in each fixed-first-coordinate
fibre of every solution code. -/
theorem columnInjectiveOn_of_holds {A : Type u} (C : A × A → Prop)
    (f : A → A → A) (d : Decoders A)
    (hholds : ∀ p, C p → Holds f d p) :
    ColumnInjectiveOn C f := by
  intro x y y' hxy hxy' heq
  have hy := hholds (x, y) hxy
  have hy' := hholds (x, y') hxy'
  calc
    y = d.column x (f x y) := hy.column_decode.symm
    _ = d.column x (f x y') := congrArg (d.column x) heq
    _ = y' := hy'.column_decode

/-- The final two decoders force the ordered superposition map to be
injective on every solution code. -/
theorem superpositionInjectiveOn_of_holds {A : Type u}
    (C : A × A → Prop) (f : A → A → A) (d : Decoders A)
    (hholds : ∀ p, C p → Holds f d p) :
    SuperpositionInjectiveOn C f := by
  intro p q hp hq himage
  have hp' := hholds p hp
  have hq' := hholds q hq
  have hfirst : p.1 = q.1 := by
    calc
      p.1 = d.first (superposition f p).1 (superposition f p).2 :=
        hp'.first_decode.symm
      _ = d.first (superposition f q).1 (superposition f q).2 := by
        rw [himage]
      _ = q.1 := hq'.first_decode
  have hsecond : p.2 = q.2 := by
    calc
      p.2 = d.second (superposition f p).1 (superposition f p).2 :=
        hp'.second_decode.symm
      _ = d.second (superposition f q).1 (superposition f q).2 := by
        rw [himage]
      _ = q.2 := hq'.second_decode
  exact Prod.ext hfirst hsecond

/-- On an input of the form `(f x y, y)`, choose the unique admissible
first coordinate; use an arbitrary default off the prescribed code. -/
noncomputable def rowDecoder {A : Type u} [Nonempty A]
    (f : A → A → A) (C : A × A → Prop) : A → A → A := by
  classical
  intro u y
  exact if h : ∃ x, C (x, y) ∧ f x y = u then Classical.choose h
    else Classical.choice inferInstance

theorem rowDecoder_spec {A : Type u} [Nonempty A]
    (f : A → A → A) (C : A × A → Prop)
    (hrow : RowInjectiveOn C f) {x y : A} (hC : C (x, y)) :
    rowDecoder f C (f x y) y = x := by
  classical
  let hex : ∃ x', C (x', y) ∧ f x' y = f x y := ⟨x, hC, rfl⟩
  rw [rowDecoder, dif_pos hex]
  exact hrow (Classical.choose_spec hex).1 hC
    (Classical.choose_spec hex).2

/-- On an input of the form `(x, f x y)`, choose the unique admissible
second coordinate. -/
noncomputable def columnDecoder {A : Type u} [Nonempty A]
    (f : A → A → A) (C : A × A → Prop) : A → A → A := by
  classical
  intro x u
  exact if h : ∃ y, C (x, y) ∧ f x y = u then Classical.choose h
    else Classical.choice inferInstance

theorem columnDecoder_spec {A : Type u} [Nonempty A]
    (f : A → A → A) (C : A × A → Prop)
    (hcolumn : ColumnInjectiveOn C f) {x y : A} (hC : C (x, y)) :
    columnDecoder f C x (f x y) = y := by
  classical
  let hex : ∃ y', C (x, y') ∧ f x y' = f x y := ⟨y, hC, rfl⟩
  rw [columnDecoder, dif_pos hex]
  exact hcolumn (Classical.choose_spec hex).1 hC
    (Classical.choose_spec hex).2

/-- Choose the unique admissible pair with a prescribed superposition image,
using an arbitrary default outside that image. -/
noncomputable def superRepresentative {A : Type u} [Nonempty A]
    (f : A → A → A) (C : A × A → Prop) (uv : A × A) : A × A := by
  classical
  exact if h : ∃ p, C p ∧ superposition f p = uv then Classical.choose h
    else Classical.choice inferInstance

theorem superRepresentative_spec {A : Type u} [Nonempty A]
    (f : A → A → A) (C : A × A → Prop)
    (hsuper : SuperpositionInjectiveOn C f) {p : A × A} (hC : C p) :
    superRepresentative f C (superposition f p) = p := by
  classical
  let hex : ∃ q, C q ∧ superposition f q = superposition f p :=
    ⟨p, hC, rfl⟩
  rw [superRepresentative, dif_pos hex]
  exact hsuper (Classical.choose_spec hex).1 hC
    (Classical.choose_spec hex).2

/-- Decoder extension constructed from the three partial-SOLS injectivity
conditions. -/
noncomputable def extensionDecoders {A : Type u} [Nonempty A]
    (f : A → A → A) (C : A × A → Prop) : Decoders A where
  row := rowDecoder f C
  column := columnDecoder f C
  first := fun u v => (superRepresentative f C (u, v)).1
  second := fun u v => (superRepresentative f C (u, v)).2

/-- Converse half of the partial-SOLS lemma: the three injectivity conditions
extend to total decoder maps satisfying all four equations on `C`. -/
theorem extensionDecoders_hold {A : Type u} [Nonempty A]
    (f : A → A → A) (C : A × A → Prop)
    (hrow : RowInjectiveOn C f) (hcolumn : ColumnInjectiveOn C f)
    (hsuper : SuperpositionInjectiveOn C f) {p : A × A} (hC : C p) :
    Holds f (extensionDecoders f C) p := by
  have hrep := superRepresentative_spec f C hsuper hC
  exact
    { row_decode := rowDecoder_spec f C hrow hC
      column_decode := columnDecoder_spec f C hcolumn hC
      first_decode := congrArg Prod.fst hrep
      second_decode := congrArg Prod.snd hrep }

/-- Every admissible partial code embeds into the solution set of its decoder
extension. -/
noncomputable def codeEmbeddingExtensionSolutions {A : Type u} [Nonempty A]
    (f : A → A → A) (C : A × A → Prop)
    (hrow : RowInjectiveOn C f) (hcolumn : ColumnInjectiveOn C f)
    (hsuper : SuperpositionInjectiveOn C f) :
    {p : A × A // C p} ↪ Solutions f (extensionDecoders f C) where
  toFun p := ⟨p.1, extensionDecoders_hold f C hrow hcolumn hsuper p.2⟩
  inj' := by
    intro p q hpq
    apply Subtype.ext
    exact congrArg (fun s : Solutions f (extensionDecoders f C) => s.1) hpq

/-- Cardinal form of the converse: total decoder extensions attain at least
the size of the prescribed partial SOLS code. -/
theorem code_card_le_extension_solutions {A : Type u} [Finite A] [Nonempty A]
    (f : A → A → A) (C : A × A → Prop)
    (hrow : RowInjectiveOn C f) (hcolumn : ColumnInjectiveOn C f)
    (hsuper : SuperpositionInjectiveOn C f) :
    Nat.card {p : A × A // C p} ≤
      Nat.card (Solutions f (extensionDecoders f C)) := by
  letI : Finite {p : A × A // C p} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Finite (Solutions f (extensionDecoders f C)) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Nat.card_le_card_of_injective
    (codeEmbeddingExtensionSolutions f C hrow hcolumn hsuper)
    (codeEmbeddingExtensionSolutions f C hrow hcolumn hsuper).injective

/-- A standard SOLS solution set automatically has all three partial-SOLS
properties. -/
theorem solutionSet_is_partialSOLS {A : Type u} (f : A → A → A)
    (d : Decoders A) :
    RowInjectiveOn (fun p => Holds f d p) f ∧
    ColumnInjectiveOn (fun p => Holds f d p) f ∧
    SuperpositionInjectiveOn (fun p => Holds f d p) f := by
  refine ⟨rowInjectiveOn_of_holds _ f d ?_,
    columnInjectiveOn_of_holds _ f d ?_,
    superpositionInjectiveOn_of_holds _ f d ?_⟩ <;>
    intro p hp <;> exact hp

/-- For a Latin operation, choose one representative of every superposition
fibre and use its coordinates as the last two decoders. -/
noncomputable def rSOLSDecoders {A : Type u} [Nonempty A]
    (f : A → A → A) : Decoders A where
  row := rowDecoder f (fun _ => True)
  column := columnDecoder f (fun _ => True)
  first := fun u v =>
    (Dispersion.sectionDecoder (superposition f) (u, v)).1
  second := fun u v =>
    (Dispersion.sectionDecoder (superposition f) (u, v)).2

/-- Under the Latin row/column conditions, the SOLS equations for the chosen
decoders hold exactly at the selected representatives of the superposition
fibres. -/
theorem rSOLS_holds_iff_selected {A : Type u} [Nonempty A]
    (f : A → A → A)
    (hrow : RowInjectiveOn (fun _ => True) f)
    (hcolumn : ColumnInjectiveOn (fun _ => True) f)
    (p : A × A) :
    Holds f (rSOLSDecoders f) p ↔
      Dispersion.sectionDecoder (superposition f) (superposition f p) = p := by
  constructor
  · intro hp
    apply Prod.ext
    · simpa [rSOLSDecoders] using hp.first_decode
    · simpa [rSOLSDecoders] using hp.second_decode
  · intro hp
    exact
      { row_decode := rowDecoder_spec f (fun _ => True) hrow trivial
        column_decode := columnDecoder_spec f (fun _ => True) hcolumn trivial
        first_decode := by
          simpa [rSOLSDecoders] using congrArg Prod.fst hp
        second_decode := by
          simpa [rSOLSDecoders] using congrArg Prod.snd hp }

/-- Exact equivalence between the selected representatives and the standard
SOLS solution set obtained from the four constructed decoders. -/
noncomputable def selectedEquivRSOLSSolutions {A : Type u} [Nonempty A]
    (f : A → A → A)
    (hrow : RowInjectiveOn (fun _ => True) f)
    (hcolumn : ColumnInjectiveOn (fun _ => True) f) :
    TypeEquiv
      (Dispersion.DecoderSolutions (superposition f)
        (Dispersion.sectionDecoder (superposition f)))
      (Solutions f (rSOLSDecoders f)) where
  toFun p := ⟨p.1, (rSOLS_holds_iff_selected f hrow hcolumn p.1).2 p.2⟩
  invFun p := ⟨p.1, (rSOLS_holds_iff_selected f hrow hcolumn p.1).1 p.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Formal core of the manuscript's `r`-SOLS lemma: if `r` is the cardinality
of the superposition image of a finite Latin operation, there are four total
decoders with exactly `r` satisfying ordered pairs. -/
theorem rSOLS_solutionCard_eq_image {A : Type u} [Finite A] [Nonempty A]
    (f : A → A → A)
    (hrow : RowInjectiveOn (fun _ => True) f)
    (hcolumn : ColumnInjectiveOn (fun _ => True) f) :
    Nat.card (Solutions f (rSOLSDecoders f)) =
      Nat.card (Dispersion.ImagePoints (superposition f)) := by
  have himage := Nat.card_congr
    (Dispersion.imageEquivSectionSolutions (superposition f)).toEquiv
  have hselected := Nat.card_congr
    (selectedEquivRSOLSSolutions f hrow hcolumn).toEquiv
  exact (himage.trans hselected).symm

end Examples.PartialSOLS

end TermCoding
