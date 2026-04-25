import Mathlib.Tactic
import QEC.Stabilizer.Lattice.ToricOperatorChains
import QEC.Stabilizer.Lattice.ToricHomology
import QEC.Stabilizer.Codes.ToricCodeN
import QEC.Stabilizer.Core.LogicalOperators

namespace Quantum
namespace Stabilizer
namespace Lattice

open scoped BigOperators

/-- Predicate: encoded X-chain operator commutes with every Z-check generator. -/
def xCommutesWithZChecks (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) : Prop :=
  let g := toricXOperatorOfChain L c
  ∀ z ∈ StabilizerGroup.ToricCodeN.ZGenerators L, z * g = g * z

/-- Predicate: encoded X-chain operator is a product of X plaquette generators. -/
def xIsPlaquetteProduct (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) : Prop :=
  let g := toricXOperatorOfChain L c
  g ∈ Subgroup.closure (StabilizerGroup.ToricCodeN.XGenerators L)

/-- Commutation criterion: X-chain commutes with all Z checks iff it is a cycle. -/
theorem xCommutesWithZChecks_iff_mem_toricCycles (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) :
    xCommutesWithZChecks L c ↔ c ∈ toricCycles (L := L) := by
  sorry

/-- Stabilizer criterion: X-chain is plaquette product iff it is a boundary. -/
theorem xIsPlaquetteProduct_iff_mem_toricBoundaries (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) :
    xIsPlaquetteProduct L c ↔ c ∈ toricBoundaries (L := L) := by
  sorry

/-- X nontrivial logical iff corresponding chain is cycle-not-boundary. -/
theorem xNontrivialLogical_iff_cycle_not_boundary (L : ℕ) [Fact (2 ≤ L)] (c : C1 L) :
    StabilizerGroup.IsNontrivialLogicalOperator
        (toricXOperatorOfChain L c) (StabilizerGroup.ToricCodeN.stabilizerGroup L) ↔
      c ∈ toricCycles (L := L) ∧ c ∉ toricBoundaries (L := L) := by
  sorry

end Lattice
end Stabilizer
end Quantum

