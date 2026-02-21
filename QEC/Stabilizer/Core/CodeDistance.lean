import QEC.Stabilizer.Core.StabilizerCode
import QEC.Stabilizer.Core.LogicalOperators
import QEC.Stabilizer.PauliGroup.NQubitElement

namespace Quantum
namespace StabilizerGroup

variable {n k : ℕ}

/-!
# Code distance [[n, k, d]]

The **code distance** d of a stabilizer code is the minimum Pauli weight among
nontrivial logical operators that act nontrivially on the physical qubits (weight > 0).
Phase-only elements (e.g. -1) have weight 0 and are excluded so that distance is
meaningful. A code with distance d can detect any error of weight < d and
correct any error of weight < d/2.
-/

open NQubitPauliGroupElement

/-- The code C has distance d if:
  1. d ≥ 1.
  2. Every nontrivial logical operator with positive weight has weight ≥ d.
  3. There exists some nontrivial logical operator of weight exactly d. -/
def HasCodeDistance (C : StabilizerCode n k) (d : ℕ) : Prop :=
  d ≥ 1 ∧
  (∀ g, IsNontrivialLogicalOperator g C.toStabilizerGroup → 0 < weight g → weight g ≥ d) ∧
  (∃ g, IsNontrivialLogicalOperator g C.toStabilizerGroup ∧ weight g = d)

/-- If C has distance d, then d ≥ 1. -/
theorem HasCodeDistance.one_le_d (C : StabilizerCode n k) (d : ℕ) (h : HasCodeDistance C d) :
    d ≥ 1 :=
  h.1

/-- If C has distance d, then every nontrivial logical with positive weight has weight ≥ d. -/
theorem HasCodeDistance.min_weight (C : StabilizerCode n k) (d : ℕ)
    (h : HasCodeDistance C d) (g : NQubitPauliGroupElement n)
    (hg : IsNontrivialLogicalOperator g C.toStabilizerGroup) (hw : 0 < weight g) :
    weight g ≥ d :=
  h.2.1 g hg hw

/-- If C has distance d, there exists a nontrivial logical of weight d. -/
theorem HasCodeDistance.exists_weight_eq (C : StabilizerCode n k) (d : ℕ)
    (h : HasCodeDistance C d) :
    ∃ g, IsNontrivialLogicalOperator g C.toStabilizerGroup ∧ weight g = d :=
  h.2.2

end StabilizerGroup
end Quantum
