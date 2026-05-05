import QEC.Stabilizer.Homological
import QEC.Stabilizer.Lattice.ToricHomology
import QEC.Stabilizer.Lattice.ToricH1Dimension
import QEC.Stabilizer.Lattice.ToricOperatorChains
import QEC.Stabilizer.Lattice.ToricLogicalCorrespondenceZ
import QEC.Stabilizer.Codes.ToricCodeN

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

/-- The toric edge-to-qubit equiv, built from `edgeToQubitIdx` (which is injective
between equinumerous finite types). Returns an `EdgeIdx L ≃ Fin (toricNumQubits L)`
so the abstract chain operator and the existing `toricXOperatorOfChain L` end up
in the same `NQubitPauliGroupElement (2 * L * L)` type. -/
noncomputable def toricEdgeEquiv (L : ℕ) [Fact (0 < L)] :
    EdgeIdx L ≃ Fin (Quantum.Stabilizer.Lattice.toricNumQubits L) := by
  have hbij : Function.Bijective
      (Quantum.Stabilizer.Lattice.edgeToQubitIdx L) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨Quantum.Stabilizer.Lattice.edgeToQubitIdx_injective L, ?_⟩
    simp [Quantum.Stabilizer.Lattice.toricNumQubits, card_edgeIdx]
  exact Equiv.ofBijective (Quantum.Stabilizer.Lattice.edgeToQubitIdx L) hbij

/-- The toric chain complex as a `HomologicalCode`.  The 0-cells are vertices,
1-cells are edges, 2-cells are faces.  The boundary maps and the chain-complex
law `∂₁ ∘ ∂₂ = 0` are imported from `ToricBoundaryMaps`.  The qubit indexing
is the same `edgeToQubitIdx` used elsewhere in the toric files. -/
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
  numQubits := Quantum.Stabilizer.Lattice.toricNumQubits L
  numQubits_eq := card_edgeIdx L
  edgeEquiv := toricEdgeEquiv L

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

/-- The toric `HomologicalCode`'s `numQubits` is definitionally `2 * L * L`. -/
theorem toricHomologicalCode_numQubits (L : ℕ) [Fact (0 < L)] :
    (toricHomologicalCode L).numQubits = 2 * L * L := rfl

/-- Definitional bridge: the abstract `numQubits` is the toric `numQubits`. -/
theorem toricHomologicalCode_numQubits_eq (L : ℕ) [Fact (0 < L)] :
    (toricHomologicalCode L).numQubits =
      Quantum.StabilizerGroup.ToricCodeN.numQubits L := rfl

/-- The abstract `chainXOperator` of the toric chain complex is the existing
`toricXOperatorOfChain`.  This holds because both operators are defined by the
same `if ∃ e, edgeToQubitIdx L e = q ∧ c e = 1 then X else I` formula, and the
toric instance's `edgeEquiv` is `Equiv.ofBijective (edgeToQubitIdx L) _`. -/
theorem toricHomologicalCode_chainXOperator_eq (L : ℕ) [Fact (0 < L)] (c : C1 L) :
    (toricHomologicalCode L).chainXOperator c = toricXOperatorOfChain L c := rfl

/-- Same for Z. -/
theorem toricHomologicalCode_chainZOperator_eq (L : ℕ) [Fact (0 < L)] (c : C1 L) :
    (toricHomologicalCode L).chainZOperator c = toricZOperatorOfChain L c := rfl

end Lattice
end Stabilizer
end Quantum
