import QEC.Stabilizer.Homological
import QEC.Stabilizer.Lattice.ToricHomology
import QEC.Stabilizer.Lattice.ToricH1Dimension

/-!
# §E — Toric chain complex as an instance of `HomologicalCode`

The toric code is the canonical instance of the generic `HomologicalCode`
abstraction.  This file packages the toric boundary maps as a `HomologicalCode`
and proves the basic identities relating the toric-specific submodules
(`toricCycles`, `toricBoundaries`, `toricH1`) to the generic versions on
`toricHomologicalCode L`.

Existing toric proofs continue to operate on the lattice-specific
definitions.  The benefit of the abstraction layer is that any new
homological CSS code (e.g. the rotated surface code, color codes,
hypergraph product codes) only needs to define its own `HomologicalCode`
instance to inherit the cycles/boundaries/H₁ infrastructure, the chain
operators with `_zero`/`_add` homomorphism lemmas, the stabilizer generators
with pairwise commutation, the centralizer-membership logical-correspondence
iffs, and the CSS distance bridge `not_both_boundary_of_nontrivial`.
-/

namespace Quantum
namespace Stabilizer
namespace Lattice

/-- The toric chain complex as a `HomologicalCode`.  The 0-cells are vertices,
1-cells are edges, 2-cells are faces.  The boundary maps and the chain-complex
law `∂₁ ∘ ∂₂ = 0` are imported from `ToricBoundaryMaps`. -/
noncomputable def toricHomologicalCode (L : ℕ) [Fact (0 < L)] :
    Quantum.Stabilizer.Homological.HomologicalCode where
  C0 := VtxIdx L
  C1 := EdgeIdx L
  C2 := FaceIdx L
  decEq0 := inferInstance
  decEq1 := inferInstance
  decEq2 := inferInstance
  fin0 := inferInstance
  fin1 := inferInstance
  fin2 := inferInstance
  boundary1 := toricBoundary1 (L := L)
  boundary2 := toricBoundary2 (L := L)
  boundary_comp := toricBoundary_comp_zero (L := L)

/-- The toric cycle submodule equals the generic version on `toricHomologicalCode L`. -/
theorem toricHomologicalCode_cycles_eq (L : ℕ) [Fact (0 < L)] :
    toricCycles (L := L) = (toricHomologicalCode L).cycles := rfl

/-- The toric boundary submodule equals the generic version. -/
theorem toricHomologicalCode_boundaries_eq (L : ℕ) [Fact (0 < L)] :
    toricBoundaries (L := L) = (toricHomologicalCode L).boundaries := rfl

/-- The toric H₁ definition agrees with the generic version. -/
theorem toricHomologicalCode_H1_eq (L : ℕ) [Fact (0 < L)] :
    toricH1 (L := L) = (toricHomologicalCode L).H1 := rfl

/-- The toric `boundaries ≤ cycles` follows from the generic chain-complex law. -/
theorem toricHomologicalCode_boundaries_le_cycles (L : ℕ) [Fact (0 < L)] :
    toricBoundaries (L := L) ≤ toricCycles (L := L) :=
  (toricHomologicalCode L).boundaries_le_cycles

/-- The number of qubits in the toric code equals the generic `numQubits` of its
chain complex (= `Fintype.card (EdgeIdx L) = 2L²`). -/
theorem toricHomologicalCode_numQubits (L : ℕ) [Fact (0 < L)] :
    (toricHomologicalCode L).numQubits = 2 * L * L := by
  show Fintype.card (EdgeIdx L) = 2 * L * L
  exact card_edgeIdx L

end Lattice
end Stabilizer
end Quantum
