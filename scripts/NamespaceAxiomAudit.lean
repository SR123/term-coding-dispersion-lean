import TermCodingDispersion
import Lean.Util.CollectAxioms
/-!
Namespace-wide axiom audit for the Paper 2 (V6) formalisation.  Scans every
constant in the `TermCoding` namespace (this includes the reused Paper 1
development and every `TermCoding.Dispersion.*` module, verified and
conditional) and fails (non-zero exit) if any of them depends on an axiom
other than `propext`, `Classical.choice`, `Quot.sound`.  Run with
`lake env lean scripts/NamespaceAxiomAudit.lean`.

The fast path collects the axioms of all `TermCoding` constants with one
shared visited-set; only if that union contains a forbidden axiom does the
script attribute it constant by constant.
-/
open Lean

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def runAudit : CoreM Unit := do
  let env ← getEnv
  let mut names : Array Name := #[]
  for (n, _) in env.constants.map₁ do
    if (`TermCoding).isPrefixOf n then names := names.push n
  IO.println s!"TermCoding constants scanned: {names.size}"
  let mut dispersion := 0
  for n in names do
    if (`TermCoding.Dispersion).isPrefixOf n then dispersion := dispersion + 1
  IO.println s!"  of which in TermCoding.Dispersion: {dispersion}"
  -- fast path: one shared traversal state
  let mut st : CollectAxioms.State := {}
  for n in names do
    let (_, s) := ((CollectAxioms.collect n).run env).run st
    st := s
  let used := st.axioms
  let bad := used.filter (fun ax => !(allowedAxioms.contains ax))
  IO.println s!"axioms used by the namespace: {used}"
  if bad.isEmpty then
    IO.println s!"OK: all TermCoding constants depend only on {allowedAxioms}"
  else
    -- slow path: attribute forbidden axioms to constants
    let mut culprits : Array (Name × Name) := #[]
    for n in names do
      let (_, s) := ((CollectAxioms.collect n).run env).run {}
      for ax in s.axioms do
        if !(allowedAxioms.contains ax) then culprits := culprits.push (n, ax)
    for (n, ax) in culprits do IO.println s!"  {n} uses {ax}"
    throwError s!"{culprits.size} constant(s) depend on axioms outside the allowlist"

#eval runAudit
