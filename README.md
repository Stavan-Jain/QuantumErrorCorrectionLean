# Quantum Error Correction in Lean

[![Lean V4](https://img.shields.io/badge/Lean-V4-blueviolet)](https://lean-lang.org/)
[![Blueprint](https://img.shields.io/badge/blueprint-live-success)](https://stavan-jain.github.io/QECLean/)
[![Dashboard](https://img.shields.io/badge/pipeline%20dashboard-live-success)](https://stavan-jain.github.io/qec-lab/)
[![Research: qec-lab](https://img.shields.io/badge/research-qec--lab-informational)](https://github.com/Stavan-Jain/qec-lab)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)

This project formalizes foundational concepts in quantum error correction using the Lean 4 proof assistant, with the long-term goal of a broad formalization of Stabilizer Codes.

Along the way, it develops definitions and lemmas for reasoning about qubits, quantum states, and unitary operations, contributing toward a verified foundation for quantum computing and fault tolerance in Lean.

## Overview

Modules are written in Lean 4 and rely on [mathlib](https://github.com/leanprover-community/mathlib4) for linear algebra and other foundations. Import everything via `QEC`, or use `QEC.Foundations.Foundations` or `QEC.Stabilizer.Stabilizer` for a subset.

This repo contains **only the Lean library** — sorry-free formalizations, in the spirit of [mathlib](https://github.com/leanprover-community/mathlib4) and [cslib](https://github.com/leanprover/cslib). **Everything on `main` depends on exactly mathlib's three standard axioms — `propext`, `Classical.choice`, `Quot.sound`.** Verify any result with `#print axioms Your.Theorem`. Work that does not yet clear this bar is parked on a branch rather than merged. The research program behind it (the BB-code distance lab, the formalization pipeline, the human-readable proof write-ups, and the dashboard) lives in the companion repo [**qec-lab**](https://github.com/Stavan-Jain/qec-lab), which shares this repo's pre-split git history. New formalizations are developed there and upstreamed here by PR when complete.

### Features

- **Foundational Quantum Computing**: Core definitions for qubits, quantum states, vectors, and norms
- **Quantum Gates**: Formalized implementations of single-qubit gates (Pauli matrices, Hadamard, phase gates, etc.)
- **Tensor Products**: Utilities and proofs for composite quantum systems
- **Repetition Code**: Complete formalization of the 3-qubit bit-flip error correction code (encode/decode, logical X, recovery)
- **Stabilizer Formalism**: Single-qubit and n-qubit Pauli groups, commutation (including tactics), matrix representations, stabilizer groups, CSS structure, centralizer, and logical operators
- **Binary Symplectic Representation**: Check matrices, symplectic inner product, symplectic span, and equivalence with independent generators
- **Concrete Codes**: surface codes, 3-qubit repetition code, n-qubit repetition code, Steane 7-qubit code, Shor 9-qubit code, and quantum Hamming code
- **Toric Code, end-to-end**: For every `L ≥ 2`, the `L × L` toric code is verified as a `StabilizerCode (2L²) 2` with **distance exactly `L`**. The chain complex, `H₁ ≅ 𝔽₂²` isomorphism, `(h, v)` wrapping invariants, and CSS distance bridge are all mechanized — see the [interactive write-up](https://stavan-jain.github.io/DistanceBlog/) (or the [in-repo version in qec-lab](https://github.com/Stavan-Jain/qec-lab/blob/main/docs/distance_proof.md)) for the math, and `QEC/Stabilizer/Codes/Toric/` (code, lattice geometry, chain complex, distance) for the Lean.
- **Bivariate-bicycle codes, incl. the gross code**: IBM's `[[144,12,12]]` gross code is verified with **distance exactly 12** (see Headline results), alongside its `[[72,12,6]]` base, the `[[72,4,8]]` pair, a `[[150,8,8]] → [[300,8,16]]` two-tier instance, and a parametric free-ℤ₂ **doubling framework** (`Framework/Homological/BB*`) with cover-transfer, deck-homotopy, deck-tower, Bockstein-rank, and class base-floor (`SmallCycleData`) layers.
- **CSS concatenation**: parametric `[[n₁n₂, k₂, ≥ d₁d₂]]` concatenation with unconditional `[[49,1,9]]` (Steane ⊗ Steane) and `[[28,2,6]]` (Steane ⊗ [[4,2,2]]) instances.
- **Verified Properties**: Mechanized proofs of key properties, including the obligations used to instantiate `StabilizerCode` instances (generator count/independence/commutation, exclusion of `-I`, and logical-operator centralizer + anticommutation conditions), along with distance theorems.

## Headline results

**The gross code.** IBM's `[[144,12,12]]` bivariate-bicycle code — the flagship qLDPC code of Bravyi et al. (Nature 2024) — is a verified `StabilizerCodeWithDistance 144 12 12`:

```lean
grossStabilizerCodeWithDistance : StabilizerCodeWithDistance 144 12 12
```

The distance proof is unconditional and axiom-clean.

**The toric family.** For every `L ≥ 2`, the `L × L` toric code is a verified `[[2L², 2, L]]` stabilizer code:

```lean
theorem toricCodeN_distance_eq_L (L : ℕ) [Fact (2 ≤ L)] :
    HasCodeDistance (toricStabilizerCode L) L
```

Here `toricStabilizerCode L : StabilizerCode (numQubits L) 2` carries `n = 2L²` and `k = 2` in its type (`numQubits L` unfolds to `2 * L * L`); the theorem above supplies `d = L`.

Every step of the homological distance argument is mechanized:

- **Chain complex.** `∂₁ ∘ ∂₂ = 0` over `𝔽₂`.
- **Homology.** `dim(H₁) = 2` via rank-nullity on `∂₁` and `∂₂`.
- **Wrapping invariants.** `h(c)`, `v(c)` are well-defined on cycles, vanish on boundaries, and give an isomorphism `H₁ ≅ 𝔽₂²`.
- **Distance lower bound.** Any non-trivial cycle has weight `≥ L` (one of `h`, `v` is `1`, forcing one edge per slice across `L` disjoint slices).
- **CSS bridge.** `d = min(d_X, d_Z)`; both equal `L` by symmetry.

An in-progress accompanying expository proof is available as an [interactive write-up](https://stavan-jain.github.io/DistanceBlog/) with diagrams (or the [in-repo version in qec-lab](https://github.com/Stavan-Jain/qec-lab/blob/main/docs/distance_proof.md)).

## Blueprint

**[Read it here.](https://stavan-jain.github.io/QECLean/)** The
[dependency graph](https://stavan-jain.github.io/QECLean/dep_graph_document.html)
is the quickest way in.

A [leanblueprint](https://github.com/PatrickMassot/leanblueprint)-style
blueprint documents the architecture: ~85 nodes covering the Pauli and binary
symplectic layer, the stabilizer framework, the homological CSS machinery, and
the toric and gross-code distance spines, wired into a dependency graph.

It is generated from Lean rather than maintained alongside it, using
[LeanArchitect](https://github.com/hanwenzhu/LeanArchitect)
([arXiv:2601.22554](https://arxiv.org/abs/2601.22554)): each node's statement,
proof sketch and title live in an `@[blueprint]` annotation in
[`QECBlueprint.lean`](QECBlueprint.lean), and the `\uses` edges are read off
the real proof terms instead of being written by hand. There is therefore no
second copy of the mathematics that can drift out of date — renaming a
declaration breaks the build rather than silently orphaning a node.

The graph is filterable: picking a node restricts it to that node's transitive
dependencies — the subgraph the result rests on — and re-runs the layout on just
that part, so asking what `steane7` needs gives 22 nodes rather than all 85. The
opposite direction (everything built on a node) and a depth cut-off are there
too, and a filtered view is a shareable URL:
`dep_graph_document.html?focus=thm:gross-distance&dir=up`.

```bash
lake build QECBlueprint:blueprint && leanblueprint web
```

See [`blueprint/README.md`](blueprint/README.md) for the full workflow.

## Project Structure

Import the whole development via `QEC` (or `QEC.Foundations.Foundations`, `QEC.Stabilizer.Stabilizer`). The code is organized as:

- **`QEC/Foundations/`** — Qubits, quantum states, gates (including CNOT), and tensor products.
- **`QEC/Stabilizer/`** — Pauli groups (single- and n-qubit), binary symplectic representation (check matrices, symplectic span), stabilizer core (groups, CSS, centralizer, codespace/distance/logical-operator tools), homological/chain-complex framework incl. the BB doubling layer, lattice and toric-homology infrastructure, and concrete codes: repetition (3- and n-qubit), rotated surface code, toric code families, bivariate-bicycle instances (gross and siblings), CSS concatenation instances, quantum Hamming, Steane 7, Shor 9, `[[5,1,3]]`, `[[4,2,2]]`, `[[6,2,2]]`, and the iceberg family.

## Getting Started

### Prerequisites

- [Lean 4](https://lean-lang.org/) (this repo uses `leanprover/lean4:v4.30.0-rc2`; see `lean-toolchain`)
- [Lake](https://github.com/leanprover/lake) (bundled with Lean) and mathlib (pulled automatically by Lake)

### Building

```bash
git clone https://github.com/Stavan-Jain/QECLean
cd QECLean
lake build
```

### Working with the Code

- Open files in your Lean 4 editor (VS Code with the Lean extension, or Emacs with lean4-mode)
- Use `#check` and `#eval` commands in Lean to explore definitions
- Run `lake build` after making changes to verify your code compiles

#### Claude Code users (optional)

This repo ships a project-scoped MCP configuration in `.mcp.json` that wires
up the [lean-lsp MCP server](https://github.com/oOo0oOo/lean-lsp-mcp), giving
[Claude Code](https://claude.com/claude-code) agents in-editor access to live
proof states, mathlib search (LeanSearch, Loogle, Lean Hammer), and Lean
diagnostics. Claude Code will prompt you to approve the server on first launch.

Requirements: [`uv`](https://docs.astral.sh/uv/) on `PATH` (provides `uvx`).
[`ripgrep`](https://github.com/BurntSushi/ripgrep) is recommended for the
local-search tool. See [`CLAUDE.md`](CLAUDE.md) for the agent-side workflow.

## Contributing

Contributions are welcome! If you add new modules or definitions, please:

1. **Expose modules** through `lakefile.toml` or the umbrella module (`QEC.lean`)
2. **Update this README** if you add or rename top-level modules
3. **Follow Lean's [style guide](https://leanprover-community.github.io/style-guide.html)** and document key definitions with docstrings
4. **Add proofs** for important properties and lemmas
5. **Ensure code compiles** with `lake build`

### Code Style

- Use the `Quantum` namespace for quantum-specific definitions
- Document definitions with `/-- ... -/` docstrings (Lean doc comments)
- Use `@[simp]` attributes for lemmas that should be used by the simplifier
- Follow mathlib conventions for naming and structure

## Goals

### Near-Term Goals

- Extend the class small-cycle theorem (analytic `d ≥ 6` for a characterized family of weight-3 BB codes) toward weight-5 / `d ≥ 10` classes
- Certify a BB code with distance `> 12` end-to-end through the doubling framework (the `[[300,8,16]]` two-tier instance's remaining dangerous-sector work)
- Restore the parked formalizations on `claude/z3z6-parked` (`Z3Z6/`, `Z5Z15F2A6/`, `BaseFloors/`, the two Steane concatenations, the 3×3 rotated surface) by replacing their `native_decide` leaves with kernel checks or certificates

### Long-Term Goals

- A generic QLDPC formalization framework instantiated across code families with proven distance
- Extend logical-operator and logical-gate formalizations for topological and LDPC-style codes
- Expand formalization across broader classes of quantum codes

## Acknowledgments

Built using [Lean 4](https://lean-lang.org/) and [mathlib](https://github.com/leanprover-community/mathlib4).

## License

Released under the [Apache License 2.0](LICENSE).

## Maintainer

Maintained by Stavan Jain

A project from the **University of Wisconsin–Madison**.
