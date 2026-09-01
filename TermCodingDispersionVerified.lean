import TermCoding
import TermCoding.Dispersion.Basic
import TermCoding.Dispersion.Diamond
import TermCoding.Dispersion.SquareBijectivity
import TermCoding.Dispersion.DirectPower
import TermCoding.Dispersion.Padding
import TermCoding.Dispersion.Reductions
import TermCoding.Dispersion.OneOutput
import TermCoding.Dispersion.TermCut
import TermCoding.Dispersion.Routing
import TermCoding.Dispersion.Threshold
import TermCoding.Dispersion.ScalarLinear
import TermCoding.Dispersion.Exponent
import TermCoding.Dispersion.Paper1Bridge
import TermCoding.Dispersion.Attacks
import TermCoding.Dispersion.Experiments
import TermCoding.Dispersion.ExperimentsSigmaThree
import TermCoding.Dispersion.Landscape
import TermCoding.Dispersion.Spectrum
import TermCoding.Dispersion.SmallSpectra
import TermCoding.Dispersion.SpectrumExponent

/-!
# Root: unconditional, kernel-checked results of the Paper 2 (V6) formalisation

Every declaration reachable from this root is proved without any
project-level postulate, from Lean/Mathlib's `propext`, `Classical.choice`,
`Quot.sound` only.
Nothing here depends on the 2019 max-flow exponent theorem.
-/
