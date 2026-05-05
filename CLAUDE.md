# CLAUDE.md — agent orientation

This is a Lean 4 / mathlib formalization of the stabilizer formalism for
quantum error correction. The active math is in `QEC/`. Build with `lake build`.

## Project tour

```
QEC/
├── Foundations/         # Hilbert spaces, vectors, gates, tensor product
├── RepetitionCode/      # Classical repetition code recovery (older module)
└── Stabilizer/          # Main formalization
    ├── PauliGroupSingle/    # Single-qubit Pauli operators (X, Y, Z, I, phases)
    ├── PauliGroup/          # n-qubit Pauli group + commutation theory
    ├── BinarySymplectic/    # Symplectic representation, check matrices
    ├── Core/                # StabilizerGroup, Codespace, Centralizer,
    │                        # LogicalGates, CSS, CodeDistance abstractions
    ├── Codes/               # Concrete codes: Shor9, Steane7, Repetition*,
    │                        # Toric*, RotatedSurface3, QuantumHamming
    └── Lattice/             # Toric code lattice geometry, chains,
                             # boundary maps, homology, H¹ dimension
```

Top-level umbrella `.lean` files (e.g. `QEC/Stabilizer/Stabilizer.lean`,
`Codes.lean`, `Lattice.lean`) just re-export submodules — don't put real
content there.

## Naming and style conventions

- **Lemmas / theorems**: `snake_case`. Use `theorem` for top-level results,
  `lemma` for stepping stones.
- **Definitions**: `camelCase` (`stabilizerSum`, `mulOp`, `phasePower`,
  `toMatrix`).
- **Namespaces**: math sits under `Quantum`; type-bound lemmas sit under
  the type's namespace (`NQubitPauliGroupElement.commutes_iff_*`).
- **`noncomputable def`**: required for any def whose RHS uses
  `Subgroup.closure` or transitively goes through `NQubitPauliGroupElement.instGroup`
  (mathlib's `Group` instance on this type is noncomputable as of v4.30).
  Common pattern: every concrete code's `def subgroup` and
  `mkStabilizerFromGenerators` / `toStabilizerGroup` in `StabilizerCode.lean`.
- **Tactics**:
  - `simp +decide` is preferred over hand-written `decide` (and avoids the
    "expected type must not contain free variables" trap).
  - `native_decide` is allowed (per user preference).
  - When closing residual `if c then 1 else 0`-style goals after `simp`,
    `split_ifs <;> simp_all (config := {decide := true}) <;> first | rfl |
    exact absurd rfl ‹_›` is the common closer.
- **Sorry markers**: `sorry  -- TODO(<short-tag>): <one-line note about goal shape>`.
  Always tag so the next session can grep for them.

## Project-specific helpers (NOT mathlib)

These are local to this codebase — search here before assuming mathlib has them:

- `NQubitPauliGroupElement.toMatrix`, `.mulOp`, `.phasePower`, `.operators`
- `NQubitPauliGroupElement.Anticommute`, `.anticommutesAt`
- `NQubitPauliGroupElement.commutes_iff_even_anticommutes`
- `StabilizerGroup`, `.toSubgroup`, `.is_abelian`, `.one_mem`,
  `.neg_identity_not_mem`, `.codespaceSubmodule`
- `IsStabilizedBy`, `IsStabilizedVec`, `IsInCodespace`, `PreservesCodespaceConjugation`
- `NQubitVec`, `Vector` (= `α → ℂ`), `NQubitBasis`
- `Stabilizer.Lattice.rowMajor_injective`, `fin_ne_of_val_lt_offset_le`
- `EdgeIdx`, `FaceIdx`, `VtxIdx`, `C0`/`C1`/`C2` chains, `next`/`prev`,
  `zeroCoord`, `hEdge`/`vEdge`/`hEdgeIdx`/`vEdgeIdx`, `singleFace`
- `toricCycles`, `toricBoundaries`, `toricBoundary1`/`toricBoundary2`,
  `toricDualCycles`, `toricDualBoundaries`

## Build & verification

```
lake build                                    # whole repo (~10 min cold)
lake build QEC.Stabilizer.Core.Codespace      # one module
lake env lean /tmp/probe.lean                 # one-off file check
```

Always verify with `lake build` before claiming a fix works. The error
output prints the residual goal under each failure — read it before guessing
tactics.

## Interactive proof debugging

For tactic-level surgery, use the Lean REPL instead of the build-error loop:

```bash
# One-time setup (if not already built)
git clone --depth 1 https://github.com/leanprover-community/repl /tmp/lean-repl
cd /tmp/lean-repl && lake build  # toolchain matches the project's

# Drive it: send JSON, get JSON back. The REPL keeps proof states alive
# across calls so you can iterate tactics without rebuilding the file.
```

The driver pattern: load a file with `{"path": "...", "allTactics": false}`
to get back a list of `sorries` with their `proofState` ids. Then send
`{"tactic": "...", "proofState": N}` to try a tactic against state N.
Response includes new goals (or `proofStatus: "Completed"`).

When to use the REPL: any time you'd otherwise be guessing tactics from a
build error. When NOT to use it: simple fixes the build error already
explains, or pure refactoring.

## Forbidden / require-permission actions

**Never run these without asking the user first, every time:**

- `lake exe cache get` / `lake exe cache get!`
- `lake update`
- `rm -rf ~/.cache/mathlib`
- Any other operation that re-downloads or rebuilds large fractions of mathlib

These take 5–30+ minutes, hold the workspace lock (blocking everything else),
and have caused real corruption when run concurrently with other lake
processes. Verify alleged corruption with a cheap probe first
(`echo 'import That.Module' > /tmp/p.lean && lake env lean /tmp/p.lean`)
before reaching for the heavy hammer.

**Never run two lake processes concurrently.** They share a workspace lock
and partial writes can corrupt build artifacts (we've seen "Foo 2.ilean"
duplicates and silent olean truncation from this).

## When the Lean LSP fails to start

Run `bash scripts/prune-stale-ileans.sh`. This handles the four classes of
stale build artifacts that crash `lake serve`:

0. macOS-style duplicates (`Foo 2.ilean`)
1. Orphan ileans (source `.lean` no longer exists)
2. Stub ileans (no `decls` field — deprecation/umbrella modules)
3. Old-format ileans (reference usage tuples not length 4 or 5)

If you're upgrading the toolchain, see `TOOLCHAIN_UPGRADE.md` (gitignored,
local runbook).

## Things that broke recently in v4.30 (be aware)

- `Subgroup.normalizer` takes `Set G`, not `Subgroup G` — no dot notation.
  Write `Subgroup.normalizer S.toSubgroup` not `S.toSubgroup.normalizer`.
- `simp [ZMod, ← even_iff_two_dvd]` no longer turns `(c : ZMod 2) = 0` into
  `Even c`. Use `Finset.sum_boole` + `ZMod.natCast_eq_zero_iff_even` instead.
- `Matrix.mulVec_smul` rewrites can fail to unify when scalar type and
  matrix-entry type differ (`ℝ` vs `ℂ`). Workaround: wrap in an explicit
  `show ∀ (M : Matrix _ _ ℂ) (b : ℝ) (w : NQubitVec n), M.mulVec (b • w) =
  b • M.mulVec w from fun _ _ _ => Matrix.mulVec_smul _ _ _`.
- `push_neg` is deprecated — prefer `push Not`.
- mathlib's `Matrix.mul_eq_one_comm`, `Matrix.isUnit_of_right_inverse` are
  deprecated; use `mul_eq_one_comm` and `IsUnit.of_mul_eq_one`.
