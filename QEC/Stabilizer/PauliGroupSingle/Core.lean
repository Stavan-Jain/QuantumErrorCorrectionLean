import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic
import Mathlib.Data.Fintype.Basic

namespace Quantum

/-!
# Single-Qubit Pauli Group: Core Types

This file contains the core datatypes for the single-qubit Pauli group:

- `PauliOperator` (I, X, Y, Z)
- `PauliGroupElement` (a phase power `Fin 4` and an operator)
-/

/-- The four Pauli operators: Identity, X, Y, and Z. -/
inductive PauliOperator : Type
  | I : PauliOperator
  | X : PauliOperator
  | Y : PauliOperator
  | Z : PauliOperator
deriving DecidableEq

/-- An element of the single-qubit Pauli group.

Represented as `i^k * P` where `k : Fin 4` is the phase power and `P : PauliOperator`.
-/
structure PauliGroupElement where
  phasePower : Fin 4
  operator : PauliOperator
deriving DecidableEq

/-- Extensionality for PauliGroupElement. -/
@[ext] theorem PauliGroupElement.ext (p q : PauliGroupElement)
  (h_phase : p.phasePower = q.phasePower)
  (h_op : p.operator = q.operator) : p = q := by
  cases p; cases q; congr

end Quantum

