import QECWidgets.PauliEval
import QECWidgets.Style
import QECWidgets.PauliStrip
import QECWidgets.PauliGoalPanel
import QECWidgets.ToricLattice
import QECWidgets.CheckMatrix
import QECWidgets.Demo

/-!
# QECWidgets

ProofWidgets-based infoview widgets for the QEC library: colored per-qubit Pauli
support strips, commutation parity views, and friends. See
`QECWidgets/Demo.lean` for living usage examples.

This library is deliberately separate from `QEC` (same policy as
`QECBlueprint`): only `QECWidgets` imports ProofWidgets, so the mathematical
library keeps its dependency surface unchanged. Everything here is untrusted
display-layer meta code — widgets render what reduction finds, and proofs are
still checked by the kernel as usual.
-/
