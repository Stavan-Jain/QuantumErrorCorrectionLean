import Mathlib.Tactic
import QEC.Stabilizer.Codes.ToricCodeNDistanceX
import QEC.Stabilizer.Codes.ToricCodeNDistanceZ
import QEC.Stabilizer.Lattice.ToricLogicalCorrespondenceZ
import QEC.Stabilizer.PauliGroup.NQubitElement

namespace Quantum
namespace StabilizerGroup
namespace ToricCodeN

open scoped BigOperators
open NQubitPauliGroupElement

/-!
# Full toric-code distance = L

Combines the X-distance (from `ToricCodeNDistanceX`) and Z-distance
(from `ToricCodeNDistanceZ`) via the CSS bridge to obtain the full distance.
-/

-- ---------------------------------------------------------------------------
-- 1.  Full-distance predicate
-- ---------------------------------------------------------------------------

/-- Full-distance predicate over all nontrivial logical operators. -/
def HasToricDistance (L d : ℕ) [Fact (2 ≤ L)] : Prop :=
  d ≥ 1 ∧
  (∀ g : NQubitPauliGroupElement (numQubits L),
      IsNontrivialLogicalOperator g (stabilizerGroup L) →
      0 < weight g →
      weight g ≥ d) ∧
  (∃ g : NQubitPauliGroupElement (numQubits L),
      IsNontrivialLogicalOperator g (stabilizerGroup L) ∧
      weight g = d)

-- ---------------------------------------------------------------------------
-- 2.  CSS bridge: full distance = min(dX, dZ)
-- ---------------------------------------------------------------------------

/-
Helper definitions for the CSS bridge proof.

For a general Pauli `g`, the X-chain and Z-chain are:
  xChainOf g e = 1  iff  g.operators (edgeToQubitIdx e) ∈ {X, Y}
  zChainOf g e = 1  iff  g.operators (edgeToQubitIdx e) ∈ {Z, Y}

Key facts:
  * weight g ≥ edgeWeight (xChainOf g)   (support inclusion)
  * weight g ≥ edgeWeight (zChainOf g)
  * g commutes with all Z-vertex stabs  ↔  xChainOf g ∈ toricCycles
  * g commutes with all X-face stabs    ↔  zChainOf g ∈ toricDualCycles
  * g nontrivial  →  ¬(xChainOf g ∈ toricBoundaries ∧ zChainOf g ∈ toricDualBoundaries)
-/

/-- X-part chain of a general Pauli (1 where the operator is X or Y). -/
private noncomputable def xChainOf (L : ℕ) (g : NQubitPauliGroupElement (numQubits L)) :
    Stabilizer.Lattice.C1 L :=
  fun e =>
    if g.operators (Stabilizer.Lattice.edgeToQubitIdx L e) = PauliOperator.X ∨
       g.operators (Stabilizer.Lattice.edgeToQubitIdx L e) = PauliOperator.Y
    then 1 else 0

/-- Z-part chain of a general Pauli (1 where the operator is Z or Y). -/
private noncomputable def zChainOf (L : ℕ) (g : NQubitPauliGroupElement (numQubits L)) :
    Stabilizer.Lattice.C1 L :=
  fun e =>
    if g.operators (Stabilizer.Lattice.edgeToQubitIdx L e) = PauliOperator.Z ∨
       g.operators (Stabilizer.Lattice.edgeToQubitIdx L e) = PauliOperator.Y
    then 1 else 0

/-- Weight of `g` is at least the edge-weight of its X-chain. -/
private lemma weight_ge_edgeWeight_xChain (L : ℕ) [Fact (2 ≤ L)]
    (g : NQubitPauliGroupElement (numQubits L)) :
    weight g ≥ Stabilizer.Lattice.edgeWeight (L := L) (xChainOf L g) := by
  sorry

/-- Weight of `g` is at least the edge-weight of its Z-chain. -/
private lemma weight_ge_edgeWeight_zChain (L : ℕ) [Fact (2 ≤ L)]
    (g : NQubitPauliGroupElement (numQubits L)) :
    weight g ≥ Stabilizer.Lattice.edgeWeight (L := L) (zChainOf L g) := by
  sorry

/-- If `g` is in the centralizer, its X-chain is a primal cycle. -/
private lemma xChain_mem_toricCycles_of_centralizer (L : ℕ) [Fact (2 ≤ L)]
    (g : NQubitPauliGroupElement (numQubits L))
    (hg : g ∈ centralizer (stabilizerGroup L)) :
    xChainOf L g ∈ Stabilizer.Lattice.toricCycles (L := L) := by
  sorry

/-- If `g` is in the centralizer, its Z-chain is a dual cycle. -/
private lemma zChain_mem_toricDualCycles_of_centralizer (L : ℕ) [Fact (2 ≤ L)]
    (g : NQubitPauliGroupElement (numQubits L))
    (hg : g ∈ centralizer (stabilizerGroup L)) :
    zChainOf L g ∈ Stabilizer.Lattice.toricDualCycles (L := L) := by
  sorry

/-- For a nontrivial logical `g`, the X-chain and Z-chain cannot both be boundaries. -/
private lemma not_both_boundary_of_nontrivial (L : ℕ) [Fact (2 ≤ L)]
    (g : NQubitPauliGroupElement (numQubits L))
    (hg : IsNontrivialLogicalOperator g (stabilizerGroup L)) :
    ¬(xChainOf L g ∈ Stabilizer.Lattice.toricBoundaries (L := L) ∧
      zChainOf L g ∈ Stabilizer.Lattice.toricDualBoundaries (L := L)) := by
  sorry

/-- CSS bridge: full distance = min(dX, dZ). -/
theorem toricCodeN_distance_eq_min_dX_dZ (L dX dZ : ℕ) [Fact (2 ≤ L)]
    (hx : HasToricXDistance L dX) (hz : HasToricZDistance L dZ) :
    HasToricDistance L (Nat.min dX dZ) := by
  sorry

-- ---------------------------------------------------------------------------
-- 3.  Full distance = L
-- ---------------------------------------------------------------------------

/-- Section 8.3 endpoint: the full toric-code distance is `L`. -/
theorem toricCodeN_distance_eq_L (L : ℕ) [Fact (2 ≤ L)] :
    HasToricDistance L L := by
  have hx : HasToricXDistance L L := toricCodeN_dX_eq_L L
  have hz : HasToricZDistance L L := toricCodeN_dZ_eq_L L
  simpa using toricCodeN_distance_eq_min_dX_dZ L L L hx hz

/-- Parameter-packaging: toric family has parameters `[[2L², 2, L]]`. -/
theorem toricCodeN_parameters_statement (L : ℕ) [Fact (2 ≤ L)] :
    numQubits L = 2 * L * L ∧ HasToricDistance L L :=
  ⟨rfl, toricCodeN_distance_eq_L L⟩

end ToricCodeN
end StabilizerGroup
end Quantum
