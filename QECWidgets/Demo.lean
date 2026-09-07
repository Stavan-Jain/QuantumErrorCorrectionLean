/-
Copyright (c) 2026 Stavan Jain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stavan Jain
-/
import QEC.Stabilizer.Codes.Small.Steane7
import QECWidgets.PauliStrip
import QECWidgets.PauliGoalPanel
import QECWidgets.ToricLattice
import QECWidgets.CheckMatrix
import ProofWidgets.Component.Panel.SelectionPanel
import ProofWidgets.Component.Panel.GoalTypePanel

/-!
# Widget demos

Living usage examples for the QEC infoview widgets. Open this file in an editor
to see every widget render; it is imported by the `QECWidgets` umbrella so the
demos are compiled (and therefore cannot silently rot).

Each `#pauli_strip` below puts a widget in the infoview when the cursor is on
the command. The `example`s at the bottom show the in-proof panels.
-/

namespace QECWidgets.Demo

open Quantum Quantum.StabilizerGroup ProofWidgets
open scoped Pauli

/-! ## Single terms: generators and logicals of the Steane code -/


#pauli_strip Steane7.X1

#pauli_strip Steane7.Z2

#pauli_strip Steane7.logicalX

-- A product through the noncomputable `Mul` (reduction, not compilation),
-- with a nontrivial phase: `logicalY = i · X̄Z̄` is phase −1 on all-Y
-- (cf. `logicalY_eq_phase2_allY`).
#pauli_strip Steane7.logicalY

#pauli_strip (Steane7.X1 * Steane7.Z1)

-- An inline literal with phase −i, written with the scoped `σ[…]` construction
-- notation (`open scoped Pauli`): `-iσ[…]` is `phasePower = 3`.
#pauli_strip (-iσ[XIXXIIX])

/-! ## Propositions: commutation views -/

-- Logical X and logical Z overlap on all 7 qubits: odd, so they anticommute.
#pauli_strip (NQubitPauliGroupElement.Anticommute Steane7.logicalX Steane7.logicalZ)

-- A commutation goal in equality form: the sides agree qubit-wise and in
-- phase (4 anticommuting positions — even), so the equality holds.
#pauli_strip (Steane7.logicalX * Steane7.Z1 = Steane7.Z1 * Steane7.logicalX)

-- Anticommutation seen as a phase gap: the two products carry the same
-- operator part and differ only in the leading glyph (+i vs −i).
#pauli_strip (Steane7.logicalX * Steane7.logicalZ = Steane7.logicalZ * Steane7.logicalX)

/-! ## Check matrices -/

-- The full Steane generator list: (H | H) blocks, all-zero Gram matrix.
#check_matrix Steane7.generatorsList

-- A non-commuting list for contrast: the Gram matrix flags the logical pair.
#check_matrix [Steane7.logicalX, Steane7.logicalZ, Steane7.Z1]

/-! ## Toric lattice views -/

section Toric

open Quantum.Stabilizer.Lattice

/-- A vertical non-contractible loop on the 4 × 4 torus: the `v`-edges of column
`x = 1`. Its class generates one factor of `H₁`. -/
def zLoop : C1 4 := fun e =>
  match e with
  | .h _ _ => 0
  | .v x _ => if x = 1 then 1 else 0

/-- A horizontal *dual* loop: the `v`-edges of row `y = 2` — the support an
X-type dual cycle crosses. It shares exactly one edge with `zLoop`, namely
`v (1, 2)`. -/
def xLoop : C1 4 := fun e =>
  match e with
  | .h _ _ => 0
  | .v _ y => if y = 2 then 1 else 0

-- A bare 1-chain (neutral purple), and the same chain as a Z operator.
#toric_chain zLoop

#toric_chain (toricZOperatorOfChain 4 zLoop)

-- The same object through the Pauli-strip widget: qubit indices are
-- `edgeToQubitIdx`, so the lattice and the strip are two views of one thing.
#pauli_strip (toricZOperatorOfChain 4 zLoop)

-- The two loops cross at exactly one edge (v (1,2)), so the operators
-- anticommute — homological intersection parity, visible as one ringed cell.
#pauli_strip (NQubitPauliGroupElement.Anticommute
  (toricZOperatorOfChain 4 zLoop) (toricXOperatorOfChain 4 xLoop))

end Toric

/-! ## In-proof panels

With `GoalTypePanel`, a goal of one of the recognized proposition shapes is
rendered directly above the tactic state. With `SelectionPanel`, shift-click any
Pauli subexpression in the goal to render it. Put the cursor inside the proofs
below to try both.

The `decide` calls need `Decidable` instances at the group-element level. Same
pattern as `FiveQubit_5_1_3.lean`: these stay `local instance` because adding
them to the global pool once disrupted unrelated typeclass synthesis — see the
note in `PauliGroup/Commutation.lean`.
-/

/-- `DecidableEq` on `NQubitPauliGroupElement n` via field-wise decision.
Demo-local; see the section comment above. -/
local instance instDecidableEqNQubitPauliGroupElement (n : ℕ) :
    DecidableEq (NQubitPauliGroupElement n) := fun p q =>
  decidable_of_iff (p.phasePower = q.phasePower ∧ p.operators = q.operators)
    ⟨fun ⟨h1, h2⟩ => by cases p; cases q; simp_all,
     fun h => by cases h; exact ⟨rfl, rfl⟩⟩

/-- `Decidable (Anticommute p q)` via the local `DecidableEq`; `noncomputable`
because `*` on `NQubitPauliGroupElement` is noncomputable, but `decide` still
reduces through the kernel (`native_decide` does not work — prefer `decide`). -/
noncomputable local instance decidableAnticommute (p q : NQubitPauliGroupElement 7) :
    Decidable (NQubitPauliGroupElement.Anticommute p q) :=
  show Decidable (p * q = NQubitPauliGroupElement.minusOne 7 * (q * p)) from inferInstance

-- `pauli_strip?` renders the goal as a strip view with a parity verdict;
-- since the verdict says the goal holds, the panel offers a link that
-- replaces the `pauli_strip?` call with `decide` (the trailing `decide`
-- keeps this demo compiling meanwhile).
example : NQubitPauliGroupElement.Anticommute Steane7.logicalX Steane7.logicalZ := by
  pauli_strip?
  decide

example : NQubitPauliGroupElement.Anticommute Steane7.logicalX Steane7.logicalZ := by
  with_panel_widgets [GoalTypePanel]
    decide

example : Steane7.X1 * Steane7.Z2 = Steane7.Z2 * Steane7.X1 := by
  with_panel_widgets [SelectionPanel]
    decide

end QECWidgets.Demo
