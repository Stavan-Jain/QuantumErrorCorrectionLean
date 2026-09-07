import Mathlib.Tactic
import QEC.Stabilizer.Framework.Homological
import QEC.Stabilizer.Codes.RotatedSurface.BoundaryMaps
import QEC.Stabilizer.Geometry.GridIndexing

/-!
# Rotated-surface-code chain complex as an instance of `HomologicalCode`

Packages the boundary maps `rscBoundary1` / `rscBoundary2` from
[RotatedSurfaceBoundaryMaps](RotatedSurfaceBoundaryMaps.lean) into a generic
`HomologicalCode` instance, plus rfl-bridges relating the lattice-specific
submodules (`rscCycles`, `rscBoundaries`, `rscH1`) to the abstract versions.

The qubit indexing is the standard row-major map `(x, y) ↦ y * L + x`,
packaged via `rscQubitEquiv` as an `Equiv VtxIdx L ≃ Fin (L * L)`.
-/

namespace Quantum
namespace Stabilizer
namespace Lattice
namespace RotatedSurface

open scoped BigOperators
open scoped RotatedSurfaceChain

/-! ## Lattice-specific cycles / boundaries / `H₁`

These mirror the toric `toricCycles` / `toricBoundaries` / `toricH1`
definitions, providing a stable API surface for downstream files that
reason against the rotated-surface chain complex directly. -/

variable (L : ℕ)

/-- 1-cycles: kernel of `∂₁`. -/
def rscCycles [Fact (Odd L)] : Submodule (ZMod 2) (VtxIdx L → ZMod 2) :=
  LinearMap.ker (∂₁ L)

/-- 1-boundaries: range of `∂₂`. -/
def rscBoundaries : Submodule (ZMod 2) (VtxIdx L → ZMod 2) :=
  LinearMap.range (∂₂ L)

/-- `Z₁ L` is the rotated-surface 1-cycle submodule `rscCycles L` (`L` explicit, as for
`∂₁`). Scoped: `open scoped RotatedSurfaceChain`. The `ToricChain` scope binds the same
tokens `Z₁`/`B₁`/`H₁` to the toric submodules, so open one of the two scopes per file. -/
scoped[RotatedSurfaceChain] notation "Z₁" => Quantum.Stabilizer.Lattice.RotatedSurface.rscCycles

/-- `B₁ L` is the rotated-surface 1-boundary submodule `rscBoundaries L`.
Scoped: `open scoped RotatedSurfaceChain`. -/
scoped[RotatedSurfaceChain] notation "B₁" =>
  Quantum.Stabilizer.Lattice.RotatedSurface.rscBoundaries


/-- Every boundary is a cycle (`∂₁ ∘ ∂₂ = 0`). -/
theorem rscBoundaries_le_rscCycles [Fact (Odd L)] :
    rscBoundaries L ≤ rscCycles L := by
  intro c hc
  rcases hc with ⟨f, rfl⟩
  exact rscBoundary_comp_zero_apply L f

/-- First homology `H₁ = Z₁ / B₁` for the rotated surface code. -/
abbrev rscH1 [Fact (Odd L)] : Type :=
  Z₁ L ⧸ Submodule.comap (Z₁ L).subtype (B₁ L)

/-- `H₁ L` is the rotated-surface first homology `rscH1 L = Z₁ L ⧸ B₁ L`.
Scoped: `open scoped RotatedSurfaceChain`. -/
scoped[RotatedSurfaceChain] notation "H₁" => Quantum.Stabilizer.Lattice.RotatedSurface.rscH1


/-! ## Row-major qubit indexing -/

/-- Row-major qubit indexing: `(x, y) ↦ y * L + x`.  This is the
canonical bijection `VtxIdx L ≃ Fin (L * L)` and matches the convention
used elsewhere in the codebase (`Lattice.rowMajor_injective`). -/
def vtxToQubitIdx (p : VtxIdx L) : Fin (L * L) :=
  ⟨p.2.val * L + p.1.val, by
    have h1 := p.1.isLt
    have h2 := p.2.isLt
    calc p.2.val * L + p.1.val
        < p.2.val * L + L := by omega
      _ = (p.2.val + 1) * L := by ring
      _ ≤ L * L := Nat.mul_le_mul_right _ h2⟩

@[simp] lemma vtxToQubitIdx_val (p : VtxIdx L) :
    (vtxToQubitIdx L p).val = p.2.val * L + p.1.val := rfl

lemma vtxToQubitIdx_injective [Fact (0 < L)] :
    Function.Injective (vtxToQubitIdx L) := by
  intro p q hpq
  have h := Fin.mk.inj_iff.mp hpq
  exact rowMajor_injective L h

/-- The canonical row-major bijection `VtxIdx L ≃ Fin (L * L)`. -/
noncomputable def rscQubitEquiv [Fact (0 < L)] :
    VtxIdx L ≃ Fin (L * L) := by
  have hbij : Function.Bijective (vtxToQubitIdx L) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨vtxToQubitIdx_injective L, ?_⟩
    simp [Fintype.card_prod, Fintype.card_fin]
  exact Equiv.ofBijective _ hbij

/-! ## The `HomologicalCode` instance -/

/-- Positivity of `L` follows from `Fact (3 ≤ L)`.  Registered as an instance
so the qubit-equivalence and other `[Fact (0 < L)]`-requiring lemmas resolve
automatically downstream. -/
instance pos_of_three_le {L : ℕ} [Fact (3 ≤ L)] : Fact (0 < L) :=
  ⟨lt_of_lt_of_le (by decide : 0 < 3) Fact.out⟩

/-- The rotated-surface-code chain complex packaged as a generic
`HomologicalCode`.  Consumers of `Homological.HomologicalCode`'s API
(generic stabilizer construction, CSS distance bridge, etc.) can
operate on this without re-deriving any lattice-specific facts. -/
noncomputable def rotatedSurfaceHomologicalCode [Fact (Odd L)] [Fact (3 ≤ L)] :
    Quantum.Stabilizer.Homological.HomologicalCode where
  C0 := ZFaceIdx L
  C1 := VtxIdx L
  C2 := XFaceIdx L
  decEq0 := inferInstance
  decEq1 := inferInstance
  decEq2 := inferInstance
  fin0 := inferInstance
  fin1 := inferInstance
  fin2 := inferInstance
  boundary1 := ∂₁ L
  boundary2 := ∂₂ L
  boundary_comp := rscBoundary_comp_zero L
  numQubits := L * L
  numQubits_eq := by simp [Fintype.card_prod, Fintype.card_fin]
  edgeEquiv := rscQubitEquiv L

/-! ## RFL bridges

These all hold definitionally — the proofs are `rfl`.  They give
downstream code a stable interface for translating between
lattice-specific and abstract names. -/

variable [Fact (Odd L)] [Fact (3 ≤ L)]

theorem rotatedSurfaceHomologicalCode_C0 :
    (rotatedSurfaceHomologicalCode L).C0 = ZFaceIdx L := rfl

theorem rotatedSurfaceHomologicalCode_C1 :
    (rotatedSurfaceHomologicalCode L).C1 = VtxIdx L := rfl

theorem rotatedSurfaceHomologicalCode_C2 :
    (rotatedSurfaceHomologicalCode L).C2 = XFaceIdx L := rfl

theorem rotatedSurfaceHomologicalCode_boundary1 :
    (rotatedSurfaceHomologicalCode L).boundary1 = ∂₁ L := rfl

theorem rotatedSurfaceHomologicalCode_boundary2 :
    (rotatedSurfaceHomologicalCode L).boundary2 = ∂₂ L := rfl

theorem rotatedSurfaceHomologicalCode_numQubits :
    (rotatedSurfaceHomologicalCode L).numQubits = L * L := rfl

/-- The lattice-specific 1-cycle submodule equals the generic version. -/
theorem rotatedSurfaceHomologicalCode_cycles_eq :
    Z₁ L = (rotatedSurfaceHomologicalCode L).cycles := rfl

/-- The lattice-specific 1-boundary submodule equals the generic version. -/
theorem rotatedSurfaceHomologicalCode_boundaries_eq :
    B₁ L = (rotatedSurfaceHomologicalCode L).boundaries := rfl

/-- The lattice-specific `H₁` definition agrees with the generic one. -/
theorem rotatedSurfaceHomologicalCode_H1_eq :
    H₁ L = (rotatedSurfaceHomologicalCode L).H1 := rfl

/-- `boundaries ≤ cycles` follows from the generic chain-complex law. -/
theorem rotatedSurfaceHomologicalCode_boundaries_le_cycles :
    B₁ L ≤ Z₁ L :=
  (rotatedSurfaceHomologicalCode L).boundaries_le_cycles

end RotatedSurface
end Lattice
end Stabilizer
end Quantum
