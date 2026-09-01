import TermCoding.Dispersion.Spectrum
import TermCoding.Dispersion.Exponent

/-!
# Spectrum-level form of "perfect implies full rate"
(V10, `thm:perfect-spectrum-structure`(ii))

A nonempty perfect-alphabet spectrum forces the dispersion exponent to be
`r`.  Unconditional: the existence of the limit is Paper 1's convergence
theorem via the dispersion embedding (`dispRate_tendsto`).
-/

namespace TermCoding

namespace Dispersion

universe uSym

variable {σ : Signature.{uSym}} [Fintype σ.Symbol] {k r : Nat}

/-- `thm:perfect-spectrum-structure`(ii): a nonempty perfect-alphabet
spectrum forces `D(t) = r`. -/
theorem exponent_eq_of_spectrum_nonempty (t : Instance σ k r) (hr : 0 < r)
    (h : (perfectSpectrum t).Nonempty) :
    exponent t = r :=
  exponent_eq_of_perfect t hr ((perfectSpectrum_nonempty_iff t).1 h)

end Dispersion

end TermCoding
