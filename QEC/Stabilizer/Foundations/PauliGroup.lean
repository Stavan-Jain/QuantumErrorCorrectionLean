import QEC.Stabilizer.Foundations.PauliGroupSingle
import QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement
import QEC.Stabilizer.Foundations.PauliGroup.Notation
import QEC.Stabilizer.Foundations.PauliGroup.TransversalConjugation
import QEC.Stabilizer.Foundations.PauliGroup.Commutation
import QEC.Stabilizer.Foundations.PauliGroup.CommutationTactics
import QEC.Stabilizer.Foundations.PauliGroup.Representation

/-!
# The N-Qubit Pauli Group

This module is a thin “barrel import” that re-exports the n-qubit Pauli operator
and group development from smaller files:

- `QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator`
- `QEC.Stabilizer.Foundations.PauliGroup.NQubitElement`
- `QEC.Stabilizer.Foundations.PauliGroup.Notation` (scoped `σ[XZIX]`
  construction notation, `open scoped Pauli`)
- `QEC.Stabilizer.Foundations.PauliGroup.TransversalConjugation`
- `QEC.Stabilizer.Foundations.PauliGroup.Commutation`
- `QEC.Stabilizer.Foundations.PauliGroup.CommutationTactics` (tactics
  `pauli_comm_componentwise`, `pauli_comm_even_anticommutes`)
- `QEC.Stabilizer.Foundations.PauliGroup.Representation`
-/
