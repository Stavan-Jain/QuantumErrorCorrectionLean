import Mathlib.Tactic
import QEC.Stabilizer.Foundations.PauliGroup.Commutation
import QEC.Stabilizer.Foundations.PauliGroup.NQubitOperator

/-!
# Tactics for Pauli commutation goals

Two tactics to shorten repetitive commutation proofs in stabilizer code files:

- **`pauli_comm_componentwise [lemmas]`**: for goals `p * q = q * p` when `p`
  and `q` commute qubit-wise (e.g. both Z-type or both X-type). Applies
  `commutes_of_componentwise_commutes` and proves the componentwise equality by
  `fin_cases` + `simp`. Pass code-specific definitions in the optional
  `[lemmas]` list (e.g. `[Z1Z2, Z2Z3, logicalZ]`).

- **`pauli_comm_even_anticommutes`**: for goals `z * x = x * z` when commutation
  follows from "even number of qubits anticommute". Reduces the goal to
  `Even ((Finset.univ.filter (anticommutesAt ...)).card)`. Then prove by showing
  the filter equals a concrete finset (e.g.
  `have hfilter : (Finset.univ.filter ...) = {0,1} := by ext i; fin_cases i;
  simp [Finset.mem_filter, anticommutesAt, *, logicalX, Z1Z2, ...]`)
  then `simp [hfilter]` or `rw [hfilter]; decide`.

- **`pauli_anticomm_odd_anticommutes`**: for goals `Anticommute p q` (i.e.
  `p * q = (-1)*(q * p)`). Reduces the goal to `Odd ((filter ...).card)`. Then
  show the filter equals a concrete finset of odd size and `simp [hfilter]` or
  `rw [hfilter]; decide`.
-/

namespace Quantum.NQubitPauliGroupElement

open Lean.Parser.Tactic
open Lean

/-!
## Componentwise commutation
-/

syntax (name := pauli_comm_componentwise) "pauli_comm_componentwise"
  (" [" (simpStar <|> simpErase <|> simpLemma),*,? "]")? : tactic

macro_rules
  | `(tactic| pauli_comm_componentwise $[[$rules,*]]?) => do
    let rules' := rules.getD ⟨#[]⟩
    `(tactic| (
      apply NQubitPauliGroupElement.commutes_of_componentwise_commutes
      intro i
      fin_cases i <;>
        simp [NQubitPauliOperator.set, NQubitPauliOperator.identity, PauliOperator.mulOp,
          $rules',*]
    ))

/-!
## Even-anticommutes commutation
-/

syntax (name := pauli_comm_even_anticommutes) "pauli_comm_even_anticommutes" : tactic

macro_rules
  | `(tactic| pauli_comm_even_anticommutes) => `(tactic| (
      classical
      apply (NQubitPauliGroupElement.commutes_iff_even_anticommutes _ _).2
    ))

/-!
## Odd-anticommutes anticommutation
-/

syntax (name := pauli_anticomm_odd_anticommutes) "pauli_anticomm_odd_anticommutes" : tactic

macro_rules
  | `(tactic| pauli_anticomm_odd_anticommutes) => `(tactic| (
      classical
      apply (NQubitPauliGroupElement.anticommutes_iff_odd_anticommutes _ _).2
    ))

end Quantum.NQubitPauliGroupElement
