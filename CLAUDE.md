# CLAUDE.md — agent orientation

This is a Lean 4 / mathlib formalization of the stabilizer formalism for
quantum error correction. The active math is in `QEC/`. Build with `lake build`.

## Two-repo layout

This repo is the **library only** — polished, sorry-free Lean on `main`
(mathlib/cslib model). The research program behind it lives in the sibling
repo [**qec-lab**](https://github.com/Stavan-Jain/qec-lab) (shared pre-split
git history; tag `archive/pre-split-20260718` marks the split point):
the BB distance lab (`experiments/bb_lab/`), the formalization pipeline
(`pipeline/`, `catalog/`, the four pipeline agent specs), the narrative
docs, and the dashboard. Convention: qec-lab tooling expects this repo
checked out as a **sibling directory** (env `QECLEAN_ROOT`, default
`../QECLean`). WIP formalization branches live here (in worktrees), can be
backed up to the qec-lab remote (`git push lab <branch>` works thanks to
shared ancestry), and merge to `main` only when sorry-free. Read qec-lab's
`CLAUDE.md` before any pipeline or research work.

## Where to look for what

CLAUDE.md is the small must-read on every invocation. It carries
codebase-wide orientation, naming/style policy, layering rules, and
build/MCP workflow. Volatile or topic-scoped knowledge lives elsewhere:

- **[qec-lab: `docs/lean-patterns.md`](https://github.com/Stavan-Jain/qec-lab/blob/main/docs/lean-patterns.md)**
  — tactical patterns by code shape (CSS distance, non-CSS distance,
  parametric families, mechanical fixes). Reach for this when your current
  code matches one of its sections; add new patterns there when they're
  code-shape-specific rather than codebase-wide.
- **[qec-lab: `docs/mathlib-version-quirks.md`](https://github.com/Stavan-Jain/qec-lab/blob/main/docs/mathlib-version-quirks.md)**
  — mathlib API drift (deprecations, renames, signature changes),
  grouped by version. Add new entries there when you work around a
  mathlib version-specific quirk.
- **[`blueprint/README.md`](blueprint/README.md)** — the LeanArchitect
  blueprint: what is generated vs. hand-written, how to add a node, how to
  inspect one with `#show_blueprint`. Read before editing `QECBlueprint.lean`
  or `blueprint/`. See also the "Blueprint" section below.
- **[`QECWidgets/README.md`](QECWidgets/README.md)** — the ProofWidgets-based
  infoview widgets (`#pauli_strip`, `#toric_chain`, `#check_matrix`, and the
  expression presenters): what each renders, how meta-level reduction drives
  them, and the linter rules for adding widget files. Read before editing
  `QECWidgets/`.
- **[`QEC/Stabilizer/Codes/BivariateBicycle/README.md`](QEC/Stabilizer/Codes/BivariateBicycle/README.md)**
  — orientation for the BB family (gross d=12 proof spine, instance
  dirs, hypothesis-discharge map, engine-vs-analytic status,
  generated-file manifest). Read before any BB edit. Generated files
  carry `GENERATED FILE — DO NOT HAND-EDIT` banners: change the
  generator (see qec-lab's `experiments/bb_lab/GENERATORS.md`) and
  regenerate, landing both repos' changes together — never hand-edit
  the emitted Lean.

## Project tour

```
QEC/
├── Foundations/         # Hilbert spaces, vectors, gates, tensor product
└── Stabilizer/          # Main formalization, organized into 4 clusters
    ├── Foundations/         # Pauli + binary-symplectic algebra (the floor)
    │   ├── PauliGroupSingle/    # Single-qubit Pauli operators (X, Y, Z, I, phases)
    │   ├── PauliGroup/          # n-qubit Pauli group + commutation theory
    │   └── BinarySymplectic/    # Symplectic representation, check matrices,
    │                            # span and weight-two structure
    ├── Framework/           # Abstract stabilizer + homological theory
    │   ├── Core/                # General stabilizer formalism, split three ways:
    │   │   ├── Stabilizer/          # StabilizerGroup, Codespace, Centralizer,
    │   │   │                        # SubgroupLemmas, StabilizerCode
    │   │   ├── Logical/             # LogicalOperators, LogicalGates, LogicalCliffordAction,
    │   │   │                        # CodeDistance (distance lives with logicals)
    │   │   └── CSS/                 # CSSPredicates, CSSNoNegI, CSSCommutationLemmas,
    │   │                            # CSSDistance
    │   ├── Symplectic/          # Stabilizer ↔ symplectic bridge: IndependentEquiv,
    │   │                        # SymplecticOrthogonal, SupportLemmas (these import
    │   │                        # Core; they are NOT in Foundations)
    │   └── Homological/         # Abstract chain-complex / CSS framework:
    │                            # Code, CSS, Generators, StabGroup,
    │                            # LogicalCorrespondence, Distance, BBChainComplex
    ├── Geometry/            # Lattice-family-agnostic primitives:
    │                        # FinPeriodic, GridIndexing, CellComplexTypes
    └── Codes/               # Concrete codes, organized by family:
        ├── _TEMPLATE.lean       # Canonical structural reference for new CSS codes
        ├── BivariateBicycle/    # BB family, one subdir per instance:
        │                        # Gross/ (+ Gross/SafeFloor/). READ ITS
        │                        # README.md BEFORE EDITING — task router,
        │                        # discharge map, generated-file rules
        ├── Toric/               # Parametric L×L toric code: CodeN, Chains,
        │                        # BoundaryMaps, Homology, H1Dimension,
        │                        # LogicalCorrespondence{X,Z}, ChainComplex,
        │                        # Distance{,X,Z}, StabilizerCode (16 files)
        ├── RotatedSurface/      # parametric N (9 files, same shape as Toric)
        ├── Repetition/          # Three.lean (3-qubit) + N.lean (parametric)
        └── Small/               # Single-instance codes: Shor9, Steane7,
                                 # Steane7TransversalGates, FourQubit_4_2_2,
                                 # QuantumHamming, FiveQubit_5_1_3 (first non-CSS)
```

Everything under `Codes/` is `native_decide`-free. The instances that carried
one are parked on branch `claude/z3z6-parked`:
`BivariateBicycle/{Z3Z6,Z5Z15F2A6,BaseFloors}/`, `Codes/Concat/` (both Steane
concatenations), `RotatedSurface/Three.lean`, and `Small/Steane7Distance.lean`.
`Framework/` keeps the abstract machinery they exercised — notably
`Framework/Concatenation/`, which now has no concrete instance in this tree.

**Layering** (lower can be imported by higher; not the reverse):

```
Foundations  <  {Geometry, Framework.Core}  <  Framework.{Symplectic, Homological}  <  Codes
```

Top-level umbrella `.lean` files at the *sibling* level of each directory
(`QEC/Stabilizer/Foundations.lean`, `Framework.lean`, `Geometry.lean`,
`Codes.lean`, `Stabilizer.lean`) just re-export submodules — don't put real
content there. Same convention for the sub-umbrellas
(`Framework/Core/Stabilizer.lean`, etc.).

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
  - **`native_decide` is banned** — it puts a compiler-trust axiom in the
    proof term. See "Axiom policy" below. Use `decide`, `decide +kernel`,
    or an explicit certificate instead.
  - **Probing residual goals**: prefer the `lean_goal` MCP tool (see "Agent
    tooling" below) — it returns the live `goals_before` / `goals_after` at
    a position without any edit or rebuild. Fallback when the MCP isn't
    available: replace the failing tactic tail with `(try sorry)` and
    rebuild; the "declaration uses sorry" warning includes the residual
    goal state.
  - **For code-shape-specific tactical patterns** (CSS distance-2 closer,
    multi-Z anti-witness, parametric `Fin n` workarounds, backtracking
    witness search for non-CSS distance, `_root_` qualification, mechanical
    fixes), see
    [qec-lab: `docs/lean-patterns.md`](https://github.com/Stavan-Jain/qec-lab/blob/main/docs/lean-patterns.md).
    Add new patterns there, not here, unless they generalize across multiple
    code shapes.
- **Sorry markers**: `sorry  -- TODO(<short-tag>): <one-line note about goal shape>`.
  Always tag so the next session can grep for them.
- **Global vs. `local instance` discipline**: by default, declare typeclass
  instances that service a single concrete code as `local instance` *inside
  that code's file* (e.g. `Codes/FiveQubit_5_1_3.lean`). Reserve global
  instances in `PauliGroup/`, `Core/`, `BinarySymplectic/`, `Homological/`
  for genuinely reusable typeclass content. **Always run a whole-repo
  `lake build` after adding a global instance** — the typeclass synthesizer
  can take very different paths once a new instance enters the global pool,
  and unrelated proofs (especially `native_decide` ones) can break. The
  failure mode is distinctive: `failed to synthesize Decidable (∀-∃
  proposition)` on a proof that previously closed. See
  qec-lab's `pipeline/attempts/stab_5_1_3/result.md` § "Lessons learned"
  for a concrete worked example of this footgun and the locality fix.

## Axiom policy

**Everything that reaches `main` must depend on exactly mathlib's three
standard axioms — and nothing else:**

```
[propext, Classical.choice, Quot.sound]
```

Check any result with `#print axioms Your.Theorem`, or the `lean_verify` MCP
tool (it takes a fully qualified name). A declaration that prints those three,
or "does not depend on any axioms", passes. **Anything else fails**, no matter
how convincing the proof is.

**This is enforced in CI**, so a violation fails the build rather than landing
quietly. To check the whole repo the way CI does:

```bash
lake env lean scripts/AxiomCheck.lean
```

It walks every declaration defined under `QEC/` (~6.3k of them), reports each
offender with its module and the offending axioms, and exits non-zero. It is
not part of any `lean_lib`, so a normal `lake build` does not pay for it —
but it needs a completed build to run against.

The two ways this gets violated in practice:

- **`native_decide`** — evaluates the proposition with the compiled
  evaluator and seals the result behind a fresh axiom, so you are trusting
  the Lean compiler and your CPU rather than the kernel. As of v4.30 it emits
  a *per-declaration* axiom (`Your.Theorem._native.native_decide.ax_1_1`),
  not the older fixed `Lean.ofReduceBool` — so don't grep for a fixed name,
  read the `#print axioms` output. Banned.
- **`sorry`** — emits `sorryAx`. Fine on a WIP branch, never on `main`.
  Tag every one as `sorry  -- TODO(<tag>): <goal shape>` so it can be found.

Custom `axiom` declarations are equally out. If you genuinely need an
unproven input, make it a **named hypothesis** on the theorem instead — then
the assumption is visible in the statement rather than hidden in the axiom
set. `Z5Z15F2A6`'s floor inputs were the worked example of this pattern.

**What to reach for instead**, in rough order of preference: `decide`
(kernel), `decide +kernel` for the heavier finite checks, packed-`Nat` tables
instead of `Array`/`List` lookups (an `Array.getD` is an O(n) list walk under
kernel reduction), quantifier bridges so the kernel enumerates concrete
lambdas rather than whnf-ing a pi-`Fintype`, sparse rewrites in place of
`Finset.sum`s, and Gaussian-style certificates where a sweep would otherwise
be needed. The gross `[[144,12,12]]` proof under `Codes/BivariateBicycle/Gross/`
is the reference: it was converted from 135 native leaves to kernel-only, and
its capstones print the standard three. Read it before concluding a check
"has to" be native.

Code that cannot yet meet this bar does not get deleted — it gets **parked**
on `claude/z3z6-parked` with a note recording what it proves, why it was
parked, and the route back. See that branch's `PARKED-NATIVE-DECIDE.md` and
`Z3Z6/PARKED.md`. Parking preserves the work; merging it to `main` would
silently widen the trust base of everything downstream.

## Linter policy

**No `set_option linter.* false` suppressions in the codebase.** Every
warning is either fixed cleanly or left visible. Don't reach for
`set_option linter.X false in` even on tricky proofs — restructure, or
accept the visible warning and document it as out-of-scope.

The only category currently treated as out-of-scope is `linter.flexible`
on the toric proofs under `Codes/Toric/` and the rotated-surface proofs
under `Codes/RotatedSurface/` (the `simp_all +decide [...]` / `simp +decide [...]`
family). Don't introduce new sites; existing ones will be cleaned up
in a dedicated batch via the MCP union trick above.

## Linter-clean idioms

Codebase-wide style as of v4.30 (each is enforced by a corresponding
mathlib linter; don't introduce new violations):

- **`push Not at h`** instead of `push_neg at h`.
- **`refine` with `?_` placeholders** instead of `refine'` with `_`. If
  the goal is the structure-builder shorthand `refine { .. }` and `refine`
  can't infer the field metavars, spell the fields explicitly:
  `refine { toFun := ?_, map_add' := ?_, map_smul' := ?_ }`.
- **`induction k with | zero => ... | succ k ih => ...`** instead of
  `induction' k with k ih`. For closure-style induction, name cases by
  the actual principle:
  - `Subgroup.closure_induction`: `| mem g hg | one | mul x y hx hy ihx ihy | inv x hx ih`
  - `Finset.induction`: `| empty | insert a s has ih`
- **`change G`** instead of `show G` when the tactic actually rewrites
  the goal (defeq but not syntactically equal). `show` is reserved for
  readability annotations where the displayed term matches the goal up
  to alpha-equivalence.
- **`set_option maxHeartbeats N in`** must be followed by a `--` comment
  explaining why, **AFTER `... in` and BEFORE the declaration**:
  ```lean
  set_option maxHeartbeats N in
  -- why this bump is needed
  /-- doc -/
  theorem ...
  ```
  Comments placed before `set_option` don't satisfy
  `linter.style.maxHeartbeats`. The same ordering rule applies to
  `omit [Fact ...] in`: the doc-comment must come AFTER `... in`, or the
  parser rejects the intervening doc-comment.

For CSS-specific simp-set idioms (e.g. when to drop
`NQubitPauliOperator.identity`), see
[qec-lab: `docs/lean-patterns.md`](https://github.com/Stavan-Jain/qec-lab/blob/main/docs/lean-patterns.md)
§ CSS distance proofs.

## Project-specific helpers (NOT mathlib)

These are local to this codebase — search here before assuming mathlib has them:

- **`σ[…]` Pauli construction notation** (scoped — `open scoped Pauli`; defined in
  `PauliGroup/Notation.lean`): `σ[XZZXI] : NQubitPauliGroupElement 5`, with phase
  prefixes `iσ[…]` (phasePower 1), `-σ[…]` (2), `-iσ[…]` (3). Elaborates to
  **exactly** the literal `⟨phase, (NQubitPauliOperator.identity n).set i₀ op₀ …⟩`
  normal form (non-identity positions, increasing index order), so
  `rfl`/`decide`/`simp` behavior is identical to a hand-written `.set`-chain; a
  delaborator displays literal-shaped elements back as `σ[…]` in goals. The
  phase-less Pauli string is `P[…]` (`P[XZZXI] : NQubitPauliOperator 5`), which
  elaborates to exactly the bare `.set` chain and displays back as `P[…]` (an
  element with a non-literal phase shows as `⟨k, P[…]⟩`). Concrete
  literal codes (`Codes/Small/`, `Repetition/Three.lean`) use it. Parametric
  families with symbolic qubit counts / indices (`Repetition/N.lean`,
  `Iceberg/N.lean`, `Toric/CodeN.lean`) use the **symbolic form**
  `σ[n | i ↦ Z, j ↦ Z]` (same leading tokens: `iσ[n | …]`, `-σ[n | …]`,
  `-iσ[n | …]`, `P[n | …]`; letters `X`/`Y`/`Z`), which elaborates to exactly
  `⟨0, ((NQubitPauliOperator.identity n).set i Z).set j Z⟩` with the `.set`s in
  the written order, and displays back the same way.
- **Other scoped notations** (each is a pure macro onto the pre-existing term, with a
  delaborator/unexpander that is scoped with it, so a goal only ever shows syntax the
  current file can parse; bare names stay in `simp`/`rw`/`unfold` lists):
  `⟪p, q⟫ₛ` (scope `Quantum.NQubitPauliGroupElement`, `BinarySymplectic/SymplecticInner.lean`)
  = `NQubitPauliOperator.symplecticInner p.operators q.operators`;
  `U ⊳ M` (scope `Quantum`, `Foundations/Gates.lean`) = `conjBy U M` — `conjBy_def` is a
  `simp` lemma, so state conjugation lemmas in the matrix-product form — and
  `G₁ ⊗ᵍ G₂` = `tensorGate G₁ G₂` (`Foundations/Tensor.lean`);
  `a ⋆ b` = `conv a b` and `poly[x^3 + y + y^2]` for the indicator-function polynomials
  (scope `Quantum.Stabilizer.Homological.BB`, `Homological/BBChainComplex.lean`; the `+`
  is a union of distinct exponent points, so check them against the group's orders);
  `dim₂ V` = `Module.finrank (ZMod 2) V` (scope `Homology`, `Homological/Code.lean`);
  `Z₁ L`/`B₁ L`/`H₁ L` = `toricCycles L`/`toricBoundaries L`/`toricH1 L` and
  `Z¹ L`/`B¹ L` for the dual cycles/boundaries (scope `ToricChain`), and the same
  `Z₁`/`B₁`/`H₁` for `rscCycles`/`rscBoundaries`/`rscH1` (scope `RotatedSurfaceChain` —
  the two scopes bind the same tokens, so open one per file).
- `C.logicalX ℓ`/`C.logicalZ ℓ` are reducible abbreviations of `(C.logicalOps ℓ).xOp`/`.zOp`
  (`Core/Stabilizer/StabilizerCode.lean`); goals print whichever spelling a term carries.
- `NQubitPauliGroupElement.toMatrix`, `.mulOp`, `.phasePower`, `.operators`
- `NQubitPauliGroupElement.Anticommute`, `.anticommutesAt`
- `NQubitPauliGroupElement.commutes_iff_even_anticommutes` — main parity-based
  commutation lemma for general Paulis (the "count of anticommuting qubits is
  even" characterization)
- **`Decidable (NQubitPauliGroupElement.Anticommute p q)`** is a
  **file-local** instance, not a global one: `Codes/Small/FiveQubit_5_1_3.lean`
  (§ "Local Decidable instances") declares `local instance`s for
  `DecidableEq (NQubitPauliGroupElement n)` and `Decidable (Anticommute p q)`
  on top of the computable `DecidableEq (NQubitPauliOperator n)` from
  `Representation.lean`, and its 105-case weight-{1,2} anti-witness tables
  close by `decide` (the instance is `noncomputable` because `Mul` is;
  `native_decide` does **not** work — prefer `decide`). A new non-CSS code
  that needs this should copy those two instances rather than make them
  global, per the `local instance` discipline above — see the note in
  `PauliGroup/Commutation.lean` § "Decidability of equality and `Anticommute`".
- `StabilizerGroup`, `.toSubgroup`, `.is_abelian`, `.one_mem`,
  `.neg_identity_not_mem`, `.codespaceSubmodule`
- `IsNontrivialLogicalOperator` has **three** conditions (see
  `IsNontrivialLogicalOperator_iff`): in centralizer, not in subgroup, AND
  `∀ s ∈ S.toSubgroup, s.operators ≠ g.operators`. The third is easy to forget;
  it's what makes CSS-bridge arguments like `not_both_boundary_of_nontrivial`
  work (`g_X * g_Z` has the same operator part as `g`, so it can't be in the
  stabilizer).
- `IsNontrivialLogicalOperator_of_toSubgroup_eq` — translates the predicate
  between two stabilizer groups with the same `toSubgroup`. Used to convert
  `HasToricDistance`-style proofs (against `stabilizerGroup L`) into
  `HasCodeDistance`-style proofs (against `(toricStabilizerCode L).toStabilizerGroup`).
- `IsStabilizedBy`, `IsStabilizedVec`, `IsInCodespace`, `PreservesCodespaceConjugation`
- `NQubitVec`, `Vector` (= `α → ℂ`), `NQubitBasis`
- `Stabilizer.Lattice.rowMajor_injective`, `fin_ne_of_val_lt_offset_le`
- `EdgeIdx`, `FaceIdx`, `VtxIdx`, `C0`/`C1`/`C2` chains, `next`/`prev`,
  `zeroCoord`, `hEdge`/`vEdge`/`hEdgeIdx`/`vEdgeIdx`, `singleFace`, `singleVtx`
- `Stabilizer.Lattice.eq_prev_iff_next_eq` (and `.next_prev`, `.prev_next`,
  `.next_ne_self`, `.prev_ne_self`) — use these instead of unfolding `next`/`prev`
  to raw `(i + 1) % L` / `(i + L - 1) % L`; `omega` chokes on the modular
  arithmetic, but the symbolic lemmas dodge it.
- `toricCycles`, `toricBoundaries`, `toricBoundary1`/`toricBoundary2`,
  `toricDualCycles`, `toricDualBoundaries`
- `toricXOperatorOfChain`, `toricZOperatorOfChain` (and `_add`, `_zero` for
  homomorphism); `toricVertexCutMap` (LinearMap C0 → C1)
- `toricZOperatorOfChain_cutMap_singleVtx` /
  `toricXOperatorOfChain_boundary_singleFace` — bridges single-stab vertex/face
  ops to chain operators; key inputs for any homological identity proof.

## Build & verification

```
lake build                                    # whole repo (~45 s warm)
lake build QEC.Stabilizer.Framework.Core.Stabilizer.Codespace      # one module
lake env lean /tmp/probe.lean                 # one-off file check
```

Always verify with `lake build` before claiming a fix works. The error
output prints the residual goal under each failure — read it before guessing
tactics.

**`lake build` alone is NOT sufficient before pushing.** `defaultTargets` is
just `QEC`, so five things it does not touch will still fail CI. After any
change that adds, moves, or removes a module, run all six:

```bash
lake build && lake build QECLight && lake build QECBlueprint \
  && lake build QECWidgets \
  && lake env lean Playground.lean && lake env lean scripts/AxiomCheck.lean
```

- **`QECLight`** (root `QECLight.lean`) re-lists the `Codes` umbrella minus
  `BivariateBicycle`. Deliberately outside `defaultTargets`, so a module added
  to or removed from `Codes/` breaks it invisibly. Checked by the `hosted-env`
  workflow.
- **`Playground.lean`** `#check`s a few showcase declarations against
  `QECLight`. Removing or renaming one of them breaks it. Checked by
  `hosted-env`'s "Check Playground.lean elaborates" step.
- **`QECBlueprint`** (root `QECBlueprint.lean`) carries the blueprint
  annotations. Also outside `defaultTargets`. It names ~86 declarations by
  fully-qualified name, so **renaming or removing an annotated declaration
  breaks it** — and nothing else in the build will tell you. Checked by the
  `blueprint` workflow. See "Blueprint" below.
- **`QECWidgets`** (root `QECWidgets.lean`) carries the ProofWidgets-based
  infoview widgets. Also outside `defaultTargets`, so that only it imports
  ProofWidgets and `lake build` stays the plain library build. Checked by
  the "Build QECWidgets" step in `lean_action_ci`. See
  [`QECWidgets/README.md`](QECWidgets/README.md).
- **`scripts/AxiomCheck.lean`** enforces the axiom policy (see below).
  Checked by `lean_action_ci`.

`bash scripts/check-umbrellas.sh` covers the umbrella wiring *under* `QEC/`,
but by construction it does not walk these root-level files — hence the list
above. All three have been broken in practice by module removals that a green
`lake build` reported as fine.

## Blueprint

The library has a [leanblueprint](https://github.com/PatrickMassot/leanblueprint)
blueprint whose node content is generated from Lean by
[LeanArchitect](https://github.com/hanwenzhu/LeanArchitect). Read
[`blueprint/README.md`](blueprint/README.md) before touching it.

Two files, and the split between them matters:

- **`QECBlueprint.lean`** (repo root) — every node. Each is an
  `attribute [blueprint "label" (title := ...) (statement := ...) (proof := ...)]
  Fully.Qualified.Name` applied to a declaration that already exists in `QEC`.
  Nothing is defined here.
- **`blueprint/src/content.tex`** — the narrative: chapters, prose, and one
  `\inputleannode{label}` per node, which fixes the order they appear in.

Presentation lives alongside those in `blueprint/src/` as `extra-css` /
`extra-js` entries in `plastex.cfg`; `dep_graph_focus.js` is the one with real
logic in it (it narrows the dependency graph to a chosen node's transitive
dependencies). It reads the graph source back out of the upstream template's
inline `renderDot` call, so `scripts/check-blueprint-render.sh` asserts that
call's shape — if you change how the graph is rendered, read
[`blueprint/README.md`](blueprint/README.md) § "How it is wired in" first.

**The annotations are deliberately not inline on the declarations.** Inline
`@[blueprint]` would require `import Architect` in every annotated file, making
LeanArchitect a hard dependency of `QEC` for every downstream consumer.
Applying the attribute post-hoc from one module keeps `QEC` dependency-free.
Dependency inference and the `\leanok` sorry-check still work (they read the
environment); only tactic-proof docstrings are unavailable, which is why
`(proof := ...)` is written out explicitly.

Rules of thumb:

- **LaTeX goes in `/-- ... -/`, never in a `"string"`.** A Lean string literal
  reads `\mathcal` as an escape sequence and fails to parse. This applies to
  `title` too, which accepts both forms.
- **Never hand-write `\uses{}`.** LeanArchitect walks the proof term and stops
  at the nearest tagged ancestor, so the edges are true by construction.
  Tagging a new declaration mid-chain silently re-routes the edges that used to
  run past it — that is usually what you want, but check the graph.
- **Never edit anything under `.lake/build/blueprint/`** — regenerate with
  `lake build QECBlueprint:blueprint`.
- Renaming an annotated declaration breaks `lake build QECBlueprint` and
  nothing else. It is in the pre-push list above for exactly that reason.

## Worktrees: reuse the main repo's prebuilt mathlib

Fresh worktrees under `.claude/worktrees/<name>/` start with no
`.lake/packages/`, so the first `lake build` triggers a full mathlib
clone + rebuild (multiple gigabytes, ~30+ minutes, and holds the
workspace lock the whole time). The main repo at the worktree's
grandparent already has mathlib cloned and built — share it via
symlink before the first build:

```bash
# From the worktree root (e.g. .claude/worktrees/<name>/):
diff lake-manifest.json ../../../lake-manifest.json && {
  rm -rf .lake/packages
  ln -s ../../../../.lake/packages .lake/packages
}
```

The `diff` guards against bumping mathlib on the worktree branch and
silently using main's stale build. If the manifests differ, do **not**
symlink — `lake exe cache get` is the right fix, but it's on the
require-permission list (see below) so **ask the user first**.

The worktree's own `.lake/build/` stays separate — only the immutable
dependency artifacts under `.lake/packages/<pkg>/.lake/build/` are
shared, so there's no risk of cross-worktree contamination.

If `lake build` was already invoked and is partway through cloning
mathlib, killing it leaves `.lake/packages/mathlib/` in a half-cloned
state (just a `.git/` directory). `rm -rf .lake/packages` cleans it up,
then symlink as above.

**Cold-build memory cliff (16 GB machines).** The worktree's own
`.lake/build/` starts empty, so the first `lake build` compiles all of
`QEC/` — and its tail runs the three BB safe-floor kernel-`decide` leaves
(`Gross/SafeFloor/MImFloorY{0,1,4}`, ~3.75 GB peak each) concurrently.
On a 16 GB machine this can OOM-kill the build (and the session driving
it); CI adds 12 GB of swap for exactly this (see the comment in
`lean_action_ci.yml`). Locally, build the three leaves sequentially
first, then the rest:

```bash
for m in Y0 Y1 Y4; do
  lake build QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeFloor.MImFloor$m
done
lake build
```

Quit or idle the Lean LSP first — its file workers hold gigabytes too.

## Agent tooling: lean-lsp MCP

This repo ships a project-scoped MCP server in `.mcp.json`
(`uvx lean-lsp-mcp`, from [oOo0oOo/lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp)).
Claude Code prompts to approve it on first launch. Once approved, the agent
gets live LSP access — proof states, diagnostics, hover docs, mathlib
search, multi-tactic attempts — without round-tripping through `lake build`.

**The MCP tools are your default interface to the Lean compiler, not a
fallback.** Reach for `lake build` only as a final confirmation before commit —
not while iterating on a proof. The documented fallbacks elsewhere in this
file (`(try sorry)` rebuilds, greping build logs) are for when the MCP is
genuinely unavailable.

- `lean_goal` — proof state at a `(file, line[, column])`. Use instead of
  the `(try sorry)` rebuild trick.
- `lean_diagnostic_messages` — errors/warnings/sorries with severity filter.
  Use instead of greping build logs.
- `lean_multi_attempt` — try several tactics at one position in a single
  call. Use instead of the edit / `lake build` / repeat loop when probing
  candidate closers. **Reach for this when you have 3+ candidate tactics
  or want to compare goal states across them. For a single likely tactic,
  just edit + re-diagnose — that loop is faster.**
  - **`linter.flexible` union trick**: at a flagged `<;> simp_all +decide`
    site, call `lean_multi_attempt` with `["simp_all? +decide"]`. Lean
    prints separate `simp_all +decide only [...]` suggestions for each
    sibling subgoal. Take the **union** of all the suggested lemma lists
    and use it as one explicit replacement — closes the goals simp would
    close and leaves the others in the exact same form the trailing
    bullets/exact-tactics need. Same pattern with `simp? +decide` for the
    non-`_all` variant. This is the only reliable way to retire
    `linter.flexible` warnings on broadcast-tactic-heavy proofs without
    breaking the downstream tactics.
- `lean_loogle`, `lean_leansearch`, `lean_leanfinder`, `lean_state_search`,
  `lean_hammer_premise` — mathlib lemma discovery. Use **before** guessing
  names, especially for the v4.30 API-drift cases listed below.
- `lean_hover_info`, `lean_declaration_file` — confirm the current mathlib
  API at a symbol (rename- and deprecation-safe).
- `lean_local_search` — ripgrep over project + stdlib, scoped by the LSP.

**Default debug workflow when a proof doesn't close:**

1. **`lean_diagnostic_messages`** with `severity: error` to localize. Read
   the *first* error before the rest — later errors are often cascade noise.
2. For each error: if the diagnostic embeds the goal but it looks
   pre-tactic-application (e.g. wrapped in an unreduced `(fun y _ => ...) 1`
   from `closure_induction`), call **`lean_goal`** at the position to see
   the cleaner before/after split.
3. If you have 2+ candidate tactics and aren't sure which closes the goal,
   **`lean_multi_attempt`** at the position. Don't waste edits guessing.
4. Edit (via the Edit tool), then re-run `lean_diagnostic_messages` on
   just the changed file.
5. Only when all diagnostics are clean: one `lake build` as commit-time
   confirmation.

Do not run `lake build` between steps 4 and 5 — diagnostics already gave
you the answer, and a redundant build burns the workspace lock for minutes.

**Caveats for this repo:**

- The MCP's LSP shares the workspace lock with `lake build` (see "Never
  run two lake processes concurrently" below). Concretely: do not kick
  off a background `lake build` while iterating with the MCP — the LSP
  will hang waiting for the lock and the next `lean_diagnostic_messages`
  call will time out. Pick one mode at a time.
- External search tools rate-limit to 3 requests / 30s. Batch queries,
  and prefer `lean_local_search` first — it's not rate-limited and most
  "does this lemma exist" questions are answered locally.
- The MCP **does not edit files**. Use the Edit tool to apply tactics that
  `lean_multi_attempt` validated.
- If the LSP fails to start under the MCP, `bash scripts/prune-stale-ileans.sh`
  is the right first move — same root cause as an editor crash.

### Lean REPL (fallback, when MCP is unavailable)

If the MCP server is down, the raw Lean REPL still works
(`leanprover-community/repl`). Clone it, `lake build`, drive with JSON
per its README.

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

## Mathlib version drift

For workarounds to mathlib API drift (deprecations, renames, signature
changes encountered during version bumps), see
[qec-lab: `docs/mathlib-version-quirks.md`](https://github.com/Stavan-Jain/qec-lab/blob/main/docs/mathlib-version-quirks.md).
Add new entries there when you hit a version-specific quirk; don't add them
to this file (CLAUDE.md is the small must-read doc, the quirks file is the
version-grouped reference).

The "global typeclass instance can break unrelated `native_decide` proofs"
footgun is documented in the "Global vs. `local instance` discipline"
bullet in the *Naming and style conventions* section above — that's the
canonical location for the rule and its worked example
(qec-lab's `pipeline/attempts/stab_5_1_3/result.md` § "Lessons learned").

## Formalization pipeline (lives in qec-lab)

The catalog-driven pipeline for prioritizing and formalizing new QEC codes
— the EC-Zoo catalog, per-code scoring, the queue, per-code attempt state,
the moonshot research log, and the four pipeline agent specs — lives
entirely in [qec-lab](https://github.com/Stavan-Jain/qec-lab). Start with
its `CLAUDE.md`, then `docs/pipeline-usage.md` (recipes) and
`docs/pipeline.md` (architecture) there. Pipeline agents draft and prove
Lean in a checkout of *this* repo (usually a worktree) while tracking
their state in qec-lab.

## Canonical CSS code structure (`_TEMPLATE.lean`)

`QEC/Stabilizer/Codes/_TEMPLATE.lean` is the canonical structural reference
for formalizing a new CSS stabilizer code. It documents the standard
§1–§14 section breakdown (generators → generator sets → typing → cross-
commutation → all-pair commutation → −I lemma → generator list →
`StabilizerGroup` → independence → logical operators → anticommutation →
centralizer → `StabilizerCode` → distance), with variant notes for `k ≥ 2`
codes, non-CSS codes, and parametric families.

Before drafting a new code file by hand or via the
`qec-skeleton-drafter` agent (spec in qec-lab), **read `_TEMPLATE.lean`
first**. The embedded code samples there are copy-paste-ready and capture
the v4.30-era tactic patterns (notably the `_root_.mul_assoc` /
`_root_.one_mul` qualification trick and the `change` step before `rw`
after `closure_induction`).

Concrete instantiations of the template:

- `Steane7.lean` — k = 1, n = 7, fully-supported all-X / all-Z logicals
- `Shor9.lean` — k = 1, n = 9, repetition-of-cat encoding
- `RepetitionCode{3,N}.lean` — degenerate distance-1 cases
- `RotatedSurfaceCodeN*.lean` — parametric family; distance proof
  in sibling files using the homological framework
- `ToricCodeN*.lean` — parametric family with trimmed-generator packaging

## Stabilizer-code packaging (trimmed generator lists)

`StabilizerCode n k` requires `generatorsList.length = n - k` via its
`generators_length` field, i.e. an **independent** generator list.
Concrete codes whose natural generator list has redundancies (toric,
color codes, etc.) need a *trimmed* list to populate it.

For the toric code, the natural `generatorsList L` in `ToricCodeN.lean`
has length `2L²` (all vertex + face stabs), but `StabilizerCode.generators_length`
needs `numQubits L - 2 = 2L² - 2`. The packaging is therefore built
separately in `ToricCodeNStabilizerCode.lean` with a trimmed list — see
the comment at `ToricCodeN.lean:613` for the cross-reference.

**Pattern for new packagings** (see `ToricCodeNStabilizerCode.lean`):

1. Define a trimmed list `generatorsListPackaged L` whose closure equals
   the existing `(stabilizerGroup L).toSubgroup`. Closure equality requires
   showing each *dropped* generator is in the closure of the kept ones —
   i.e. the homological identities.
2. Build the `StabilizerCode n k` directly with the trimmed list as
   `generatorsList`.
3. Expose `(toricStabilizerCode L).toStabilizerGroup.toSubgroup =
   (stabilizerGroup L).toSubgroup` as a public lemma; use it to translate
   stabilizer-group-based proofs to stabilizer-code-based proofs via
   `IsNontrivialLogicalOperator_of_toSubgroup_eq`.

This keeps existing distance proofs (which run against `stabilizerGroup L`)
intact instead of forcing a downstream rewrite.

## Umbrella files (orphan-module trap)

New modules under `Codes/<family>/`, `Geometry/`, `Framework/Core/<bucket>/`,
etc. **must be imported in the relevant umbrella files**: the per-family /
per-bucket umbrella (e.g. `QEC/Stabilizer/Codes/Toric.lean`,
`Framework/Core/Stabilizer.lean`) AND, transitively, the cluster-level
umbrella (`Codes.lean`, `Framework.lean`, …). Files not in any umbrella
are unreachable from the default `lake build` target — never compiled,
never linted, errors silently hidden. `QuantumHamming.lean` sat in this
orphan state with two stale `Nat.xor_*` references that `lake build`
never surfaced. When adding a module, append the import to the immediate
umbrella; the chain to `Stabilizer.lean` takes care of itself.
`bash scripts/check-umbrellas.sh` verifies the whole tree (run it after
adding or moving modules).

## Cleanup recipes

One-time conversion patterns for linter sweeps and mathlib-version bumps
(nested `induction'` on `Fin L`, structure-builder `refine` chains hit
by `linter.style.multiGoal`, closure-induction case naming): see
[qec-lab: `docs/lean-conversion-recipes.md`](https://github.com/Stavan-Jain/qec-lab/blob/main/docs/lean-conversion-recipes.md).
Pull it in when you hit the corresponding warning class.
