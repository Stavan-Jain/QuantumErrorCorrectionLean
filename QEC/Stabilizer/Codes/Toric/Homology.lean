import Mathlib.Tactic
import QEC.Stabilizer.Codes.Toric.BoundaryMaps

namespace Quantum
namespace Stabilizer
namespace Lattice

open scoped ToricChain

variable (L : ℕ) [Fact (0 < L)]

/-- 1-cycles: kernel of `∂1`. -/
def toricCycles : Submodule (ZMod 2) (C1 L) :=
  LinearMap.ker (∂₁ (L := L))

/-- 1-boundaries: range of `∂2`. -/
def toricBoundaries : Submodule (ZMod 2) (C1 L) :=
  LinearMap.range (∂₂ (L := L))

/-- `Z₁ L` is the toric 1-cycle submodule `toricCycles L` (`L` explicit, as for `∂₁`).
Scoped: `open scoped ToricChain`. The `RotatedSurfaceChain` scope binds the same tokens
`Z₁`/`B₁`/`H₁` to the rotated-surface submodules, so open one of the two scopes per file;
the notation names the lattice constants, not the `ToricCodeN` aliases of them. -/
scoped[ToricChain] notation "Z₁" => Quantum.Stabilizer.Lattice.toricCycles

/-- `B₁ L` is the toric 1-boundary submodule `toricBoundaries L`.
Scoped: `open scoped ToricChain`. -/
scoped[ToricChain] notation "B₁" => Quantum.Stabilizer.Lattice.toricBoundaries


/-- Every boundary is a cycle (`im ∂2 ≤ ker ∂1`). -/
theorem toricBoundaries_le_toricCycles :
    B₁ L ≤ Z₁ L := by
  intro c hc
  rcases hc with ⟨f, rfl⟩
  have hcomp := toricBoundary_comp_zero_apply (L := L) f
  exact hcomp

/-- First homology `H1 = Z1/B1` for the toric chain complex over `ZMod 2`. -/
abbrev toricH1 : Type :=
  Z₁ L ⧸ Submodule.comap (Z₁ L).subtype (B₁ L)

/-- `H₁ L` is the toric first homology `toricH1 L = Z₁ L ⧸ B₁ L`.
Scoped: `open scoped ToricChain`. -/
scoped[ToricChain] notation "H₁" => Quantum.Stabilizer.Lattice.toricH1


end Lattice
end Stabilizer
end Quantum

