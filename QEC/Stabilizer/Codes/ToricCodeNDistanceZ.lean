import Mathlib.Tactic
import QEC.Stabilizer.Codes.ToricCodeN
import QEC.Stabilizer.Lattice.ToricLogicalCorrespondenceZ
import QEC.Stabilizer.Lattice.ToricDualWrappingInvariants
import QEC.Stabilizer.PauliGroup.NQubitElement

namespace Quantum
namespace StabilizerGroup
namespace ToricCodeN

open scoped BigOperators
open NQubitPauliGroupElement

/-!
# Z-distance = L for the toric code

Mirror of `ToricCodeNDistanceX`, using the dual chain complex:
  - `HasToricZDistance` predicate (analogue of `HasToricXDistance`)
  - Witness: vertical row of V-edges at y = 0  (weight L)
  - Lower bound: dual wrapping invariant argument
-/

-- ---------------------------------------------------------------------------
-- 1.  Z-distance predicate
-- ---------------------------------------------------------------------------

/-- Z-distance predicate: minimum weight of nontrivial Z-type logical operators. -/
def HasToricZDistance (L d : ℕ) [Fact (2 ≤ L)] : Prop :=
  d ≥ 1 ∧
  (∀ g : NQubitPauliGroupElement (numQubits L),
      NQubitPauliGroupElement.IsZTypeElement g →
      IsNontrivialLogicalOperator g (stabilizerGroup L) →
      0 < weight g →
      weight g ≥ d) ∧
  (∃ g : NQubitPauliGroupElement (numQubits L),
      NQubitPauliGroupElement.IsZTypeElement g ∧
      IsNontrivialLogicalOperator g (stabilizerGroup L) ∧
      weight g = d)

-- ---------------------------------------------------------------------------
-- 2.  Witness chain: a vertical row of V-edges
-- ---------------------------------------------------------------------------

/-- The canonical dual noncontractible cycle: V-edges at row `y = 0`. -/
def verticalVRowChain (L : ℕ) [Fact (0 < L)] : Stabilizer.Lattice.C1 L :=
  fun e =>
    match e with
    | Stabilizer.Lattice.EdgeIdx.h _ _ => 0
    | Stabilizer.Lattice.EdgeIdx.v _ y =>
        if y = Stabilizer.Lattice.zeroCoord L then (1 : ZMod 2) else 0

/-- Z-type Pauli operator encoded by the canonical vertical V-row. -/
def verticalVRowZOperator (L : ℕ) [Fact (0 < L)] :
    NQubitPauliGroupElement (Stabilizer.Lattice.toricNumQubits L) :=
  Stabilizer.Lattice.toricZOperatorOfChain L (verticalVRowChain L)

-- ---------------------------------------------------------------------------
-- 3.  The witness is a nontrivial dual cycle
-- ---------------------------------------------------------------------------

/-- The vertical V-row chain is a dual cycle (commutes with all face stabs). -/
theorem verticalVRowChain_mem_toricDualCycles (L : ℕ) [Fact (2 ≤ L)] :
    verticalVRowChain L ∈ Stabilizer.Lattice.toricDualCycles (L := L) := by
  sorry

/-- The vertical V-row chain is not a dual boundary. -/
theorem verticalVRowChain_not_mem_toricDualBoundaries (L : ℕ) [Fact (2 ≤ L)] :
    verticalVRowChain L ∉ Stabilizer.Lattice.toricDualBoundaries (L := L) := by
  sorry

/-- The vertical V-row chain has edge-weight `L`. -/
theorem verticalVRowChain_edgeWeight_eq_L (L : ℕ) [Fact (2 ≤ L)] :
    Stabilizer.Lattice.edgeWeight (L := L) (verticalVRowChain L) = L := by
  sorry

-- ---------------------------------------------------------------------------
-- 4.  Existence of a nontrivial Z-logical of weight L
-- ---------------------------------------------------------------------------

/-- Upper-bound witness: a nontrivial Z-type logical of weight exactly `L`. -/
theorem exists_nontrivial_z_logical_weight_eq_L (L : ℕ) [Fact (2 ≤ L)] :
    ∃ g : NQubitPauliGroupElement (numQubits L),
      NQubitPauliGroupElement.IsZTypeElement g ∧
      IsNontrivialLogicalOperator g (stabilizerGroup L) ∧
      weight g = L := by
  sorry

-- ---------------------------------------------------------------------------
-- 5.  Lower bound: every nontrivial Z-logical has weight ≥ L
-- ---------------------------------------------------------------------------

set_option maxHeartbeats 1000000 in
/-- Lower bound: every nontrivial Z-type logical operator has weight ≥ L. -/
theorem nontrivial_z_logical_weight_ge_L (L : ℕ) [Fact (2 ≤ L)]
    (g : NQubitPauliGroupElement (numQubits L))
    (hgZ : NQubitPauliGroupElement.IsZTypeElement g)
    (hgLogical : IsNontrivialLogicalOperator g (stabilizerGroup L)) :
    weight g ≥ L := by
  sorry

-- ---------------------------------------------------------------------------
-- 6.  Z-distance endpoint
-- ---------------------------------------------------------------------------

/-- Section 8.3: Z-distance equals `L`. -/
theorem toricCodeN_dZ_eq_L (L : ℕ) [Fact (2 ≤ L)] :
    HasToricZDistance L L := by
  refine ⟨?_, ?_, ?_⟩
  · have hL : 2 ≤ L := Fact.out; omega
  · intro g hgZ hgLogical _
    exact nontrivial_z_logical_weight_ge_L L g hgZ hgLogical
  · exact exists_nontrivial_z_logical_weight_eq_L L

end ToricCodeN
end StabilizerGroup
end Quantum
