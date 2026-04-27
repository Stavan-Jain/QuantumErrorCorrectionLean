import Mathlib.Tactic
import QEC.Stabilizer.Lattice.ToricBoundaryMaps

namespace Quantum
namespace Stabilizer
namespace Lattice

variable (L : ℕ) [Fact (0 < L)]

/-- 1-cycles: kernel of `∂1`. -/
def toricCycles : Submodule (ZMod 2) (C1 L) :=
  LinearMap.ker (toricBoundary1 (L := L))

/-- 1-boundaries: range of `∂2`. -/
def toricBoundaries : Submodule (ZMod 2) (C1 L) :=
  LinearMap.range (toricBoundary2 (L := L))

/-- Every boundary is a cycle (`im ∂2 ≤ ker ∂1`). -/
theorem toricBoundaries_le_toricCycles :
    toricBoundaries (L := L) ≤ toricCycles (L := L) := by
  intro c hc
  rcases hc with ⟨f, rfl⟩
  have hcomp := toricBoundary_comp_zero_apply (L := L) f
  exact hcomp

/-- First homology `H1 = Z1/B1` for the toric chain complex over `ZMod 2`. -/
abbrev toricH1 : Type :=
  toricCycles (L := L) ⧸ Submodule.comap (toricCycles (L := L)).subtype
    (toricBoundaries (L := L))

end Lattice
end Stabilizer
end Quantum

