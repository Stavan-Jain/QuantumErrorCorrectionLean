import QEC.Stabilizer.PauliGroupSingle
import QEC.Stabilizer.PauliGroup.NQubitOperator
import QEC.Stabilizer.PauliGroup.NQubitElement
import QEC.Stabilizer.PauliGroup.Commutation
import QEC.Stabilizer.PauliGroup.CommutationTactics
import QEC.Stabilizer.PauliGroup.Representation

/-!
# The N-Qubit Pauli Group

This module is a thin “barrel import” that re-exports the n-qubit Pauli operator and
group development from smaller files:

- `QEC.Stabilizer.PauliGroup.NQubitOperator`
- `QEC.Stabilizer.PauliGroup.NQubitElement`
- `QEC.Stabilizer.PauliGroup.Commutation`
- `QEC.Stabilizer.PauliGroup.CommutationTactics`
  (tactics `pauli_comm_componentwise`, `pauli_comm_even_anticommutes`)
- `QEC.Stabilizer.PauliGroup.Representation`
-/
