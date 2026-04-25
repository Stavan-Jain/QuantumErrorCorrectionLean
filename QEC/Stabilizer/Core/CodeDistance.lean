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
Nontrivial logical operators are defined at the element level as representing a
nontrivial coset of the stabilizer (in the centralizer): not the identity coset and
not a phase-only coset. Phase-only elements (e.g. -1) have weight 0 and are excluded
so that distance is meaningful. A code with distance d can detect any error of
weight < d and correct any error of weight < d/2.
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

/-- To prove `HasCodeDistance C d`, it suffices to show: d ≥ 1, there exists a
    nontrivial logical of weight d, and for every w with 1 ≤ w < d, no weight-w
    Pauli is a nontrivial logical. -/
theorem hasCodeDistance_of (C : StabilizerCode n k) (d : ℕ)
    (hd : d ≥ 1)
    (h_witness : ∃ g, IsNontrivialLogicalOperator g C.toStabilizerGroup ∧ weight g = d)
    (h_min : ∀ w, 1 ≤ w → w < d → ∀ g, weight g = w →
      ¬IsNontrivialLogicalOperator g C.toStabilizerGroup) :
    HasCodeDistance C d := by
  refine ⟨hd, ?_, h_witness⟩
  intro g hg_nontrivial hw_pos
  by_cases h : weight g < d
  · have h1 : 1 ≤ weight g := Nat.one_le_of_lt hw_pos
    exact absurd hg_nontrivial (h_min (weight g) h1 h g rfl)
  · omega

end StabilizerGroup
end Quantum
