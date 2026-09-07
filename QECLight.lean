import QEC.Foundations.Foundations
import QEC.Stabilizer.Foundations
import QEC.Stabilizer.Geometry
import QEC.Stabilizer.Framework
import QEC.Stabilizer.Codes.Toric
import QEC.Stabilizer.Codes.RotatedSurface
import QEC.Stabilizer.Codes.Repetition
import QEC.Stabilizer.Codes.Iceberg
import QEC.Stabilizer.Codes.Small

/-!
# QECLight — the library minus the memory-heavy code families

An import surface for environments that cannot afford the full build:
Codespaces, the hosted web editor (see `deploy/`), a laptop with 8 GB, or anyone
who wants to explore the stabilizer development without waiting on the
bivariate-bicycle proofs.

`QEC.lean` remains the umbrella that imports everything. This is a strict
subset, not a replacement, and it is deliberately absent from `defaultTargets`
so `lake build` still means the whole library.

## What is left out, and why

`import QEC` transitively pulls in `QEC.Stabilizer.Codes.BivariateBicycle`,
whose gross-code safe-floor leaves (`MImFloorY0/Y1/Y4`) are memory-hungry kernel
`decide` checks. Lake has no `-j` flag, so it schedules all three concurrently
at the tail of the build and their combined working set can exceed 16 GB —
`.github/workflows/lean_action_ci.yml` adds swap to get through them. That is a
reasonable price for a release build on a dedicated runner, and prohibitive for
a 4-core container or a shared server hosting many concurrent sessions. (Cost is
the only reason they are excluded: the proofs themselves are axiom-clean, like
everything else on `main`.)

`BivariateBicycle` is a leaf: outside its own directory, the only module that
imports it is the `QEC.Stabilizer.Codes` umbrella. So this file re-lists that
umbrella without it (and without `_TEMPLATE`, which is scaffolding rather than
content).

Everything else is here: the Pauli and binary-symplectic layer, the stabilizer
and homological framework, the toric and rotated-surface families, Steane, Shor,
and `[[5,1,3]]`. The concrete concatenation instances are currently parked on
`claude/z3z6-parked` (see CLAUDE.md § "Axiom policy"), so `Codes.Concat` no
longer exists to import; `Framework/Concatenation` is still included via
`QEC.Stabilizer.Framework`.

## Keeping this in sync

`scripts/check-umbrellas.sh` only walks directories under `QEC/`, so this
root-level file is outside its remit and will not be flagged if it drifts from
the `Codes` umbrella. The `hosted-env` workflow builds this target on every
change under `QEC/`, which is what catches a module added to `Codes/` but not
reflected here.

If a new code family turns out to be similarly expensive, exclude it here too.
-/
