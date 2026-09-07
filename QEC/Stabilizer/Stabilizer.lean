/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import QEC.Stabilizer.Foundations
import QEC.Stabilizer.Framework
import QEC.Stabilizer.Geometry
import QEC.Stabilizer.Codes

/-!
# Stabilizer formalism — top-level umbrella

Top-down structure of the stabilizer-code library:

1. `Foundations` — Pauli + binary-symplectic algebra (pure algebra; floor)
2. `Geometry` — lattice-family-agnostic primitives
3. `Framework` — abstract stabilizer / homological theory
4. `Codes` — concrete codes (toric, rotated-surface, repetition, small)

Layering: `Foundations < {Geometry, Framework} < Codes`.
-/
