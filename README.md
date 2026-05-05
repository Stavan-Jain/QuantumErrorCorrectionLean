# Quantum Error Correction in Lean

This project formalizes foundational concepts in quantum error correction using the Lean 4 proof assistant, with the long-term goal of a broad formalization of Stabilizer Codes.

Along the way, it develops **definitions and lemmas** for reasoning about qubits, quantum states, and unitary operations, contributing toward a verified foundation for quantum computing in Lean.

## Overview

Modules are written in Lean 4 and rely on [mathlib](https://github.com/leanprover-community/mathlib4) for linear algebra and other foundations. Import everything via `QEC`, or use `QEC.Foundations.Foundations`, `QEC.RepetitionCode.RepetitionCode`, or `QEC.Stabilizer.Stabilizer` for a subset.

### Features

- **Foundational Quantum Computing**: Core definitions for qubits, quantum states, vectors, and norms
- **Quantum Gates**: Formalized implementations of single-qubit gates (Pauli matrices, Hadamard, phase gates, etc.)
- **Tensor Products**: Utilities and proofs for composite quantum systems
- **Repetition Code**: Complete formalization of the 3-qubit bit-flip error correction code (encode/decode, logical X, recovery)
- **Stabilizer Formalism**: Single-qubit and n-qubit Pauli groups, commutation (including tactics), matrix representations, stabilizer groups, CSS structure, centralizer, and logical operators
- **Binary Symplectic Representation**: Check matrices, symplectic inner product, symplectic span, and equivalence with independent generators
- **Concrete Codes**: surface codes, 3-qubit repetition code, n-qubit repetition code, Steane 7-qubit code, Shor 9-qubit code, and quantum Hamming code
- **Toric Code, end-to-end**: For every `L ≥ 2`, the `L × L` toric code is verified as a `StabilizerCode (2L²) 2` with **distance exactly `L`**. The chain complex, `H₁ ≅ 𝔽₂²` isomorphism, `(h, v)` wrapping invariants, and CSS distance bridge are all mechanized — see [`docs/distance_proof.md`](docs/distance_proof.md) for the math and `QEC/Stabilizer/Lattice/` + `QEC/Stabilizer/Codes/ToricCodeN*.lean` for the Lean.
- **Verified Properties**: Mechanized proofs of key properties, including the obligations used to instantiate `StabilizerCode` instances (generator count/independence/commutation, exclusion of `-I`, and logical-operator centralizer + anticommutation conditions), along with distance theorems.

## Headline result

For every `L ≥ 2`, the `L × L` toric code is a verified `[[2L², 2, L]]` stabilizer code:

```lean
theorem toricCodeN_distance_eq_L (L : ℕ) [Fact (2 ≤ L)] :
    HasCodeDistance (toricStabilizerCode L) L
```

Here `toricStabilizerCode L : StabilizerCode (numQubits L) 2` carries `n = 2L²` and `k = 2` in its type (`numQubits L` unfolds to `2 * L * L`); the theorem above supplies `d = L`.

Every step of the homological distance argument is mechanized — no `sorry`s anywhere in the proof:

- **Chain complex.** `∂₁ ∘ ∂₂ = 0` over `𝔽₂`.
- **Homology.** `dim(H₁) = 2` via rank-nullity on `∂₁` and `∂₂`.
- **Wrapping invariants.** `h(c)`, `v(c)` are well-defined on cycles, vanish on boundaries, and give an isomorphism `H₁ ≅ 𝔽₂²`.
- **Distance lower bound.** Any non-trivial cycle has weight `≥ L` (one of `h`, `v` is `1`, forcing one edge per slice across `L` disjoint slices).
- **CSS bridge.** `d = min(d_X, d_Z)`; both equal `L` by symmetry.

The accompanying expository proof is in [`docs/distance_proof.md`](docs/distance_proof.md).

## Project Structure

Import the whole development via `QEC` (or `QEC.Foundations.Foundations`, `QEC.RepetitionCode.RepetitionCode`, `QEC.Stabilizer.Stabilizer`). The code is organized as:

- **`QEC/Foundations/`** — Qubits, quantum states, gates (including CNOT), and tensor products.
- **`QEC/RepetitionCode/`** — 3-qubit bit-flip code: encode/decode, logical X, and recovery with proofs.
- **`QEC/Stabilizer/`** — Pauli groups (single- and n-qubit), binary symplectic representation (check matrices, symplectic span), stabilizer core (groups, CSS, centralizer, codespace/distance/logical-operator tools), lattice and toric-homology infrastructure, and concrete codes: repetition (3- and n-qubit), rotated surface code, toric code families, quantum Hamming, Steane 7, and Shor 9.

## Getting Started

### Prerequisites

- [Lean 4](https://lean-lang.org/) (this repo uses `leanprover/lean4:v4.30.0-rc2`; see `lean-toolchain`)
- [Lake](https://github.com/leanprover/lake) (bundled with Lean) and mathlib (pulled automatically by Lake)

### Building

```bash
git clone <repository-url>
cd QuantumErrorCorrectionLean
lake build
```

### Working with the Code

- Open files in your Lean 4 editor (VS Code with the Lean extension, or Emacs with lean4-mode)
- Use `#check` and `#eval` commands in Lean to explore definitions
- Run `lake build` after making changes to verify your code compiles

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

- Continue strengthening reusable stabilizer and binary-symplectic APIs needed by larger code families
- Formalize the planar / rotated surface code distance (different boundary conditions, `H₁ ≅ 𝔽₂`)
- Generalize the homological distance argument to arbitrary CW-complex cellulations

### Long-Term Goals

- Build a generic QLDPC formalization framework first, then instantiate it with concrete code families and prove distance
- Extend logical-operator and logical-gate formalizations for topological and LDPC-style codes
- Expand formalization across broader classes of quantum codes

## Acknowledgments

Built using [Lean 4](https://lean-lang.org/) and [mathlib](https://github.com/leanprover-community/mathlib4).
