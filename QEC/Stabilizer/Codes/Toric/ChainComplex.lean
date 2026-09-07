import QEC.Stabilizer.Framework.Homological
import QEC.Stabilizer.Codes.Toric.Homology
import QEC.Stabilizer.Codes.Toric.H1Dimension
import QEC.Stabilizer.Codes.Toric.ChainOps
import QEC.Stabilizer.Codes.Toric.CodeN

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

open scoped ToricChain

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
  boundary1 := ∂₁ (L := L)
  boundary2 := ∂₂ (L := L)
  boundary_comp := toricBoundary_comp_zero (L := L)
  numQubits := Quantum.Stabilizer.Lattice.toricNumQubits L
  numQubits_eq := card_edgeIdx L
  edgeEquiv := toricEdgeEquiv L

/-- The toric cycle submodule equals the generic version on `toricHomologicalCode L`. -/
theorem toricHomologicalCode_cycles_eq (L : ℕ) [Fact (0 < L)] :
    Z₁ L = (toricHomologicalCode L).cycles := rfl

/-- The toric boundary submodule equals the generic version. -/
theorem toricHomologicalCode_boundaries_eq (L : ℕ) [Fact (0 < L)] :
    B₁ L = (toricHomologicalCode L).boundaries := rfl

/-- The toric H₁ definition agrees with the generic version. -/
theorem toricHomologicalCode_H1_eq (L : ℕ) [Fact (0 < L)] :
    H₁ L = (toricHomologicalCode L).H1 := rfl

/-- The toric `boundaries ≤ cycles` follows from the generic chain-complex law. -/
theorem toricHomologicalCode_boundaries_le_cycles (L : ℕ) [Fact (0 < L)] :
    B₁ L ≤ Z₁ L :=
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

/-! ## Generator-set bridges

The toric instance carries its own `vertexStab`, `faceStab`, `ZGenerators`,
`XGenerators` definitions (in `Codes/ToricCodeN.lean`).  The bridges below
identify each of these with the generic versions provided by the
`HomologicalCode` abstraction.

These bridges are what makes the toric correspondence / distance proofs
collapse to one-line applications of the generic theorems in
`Homological/LogicalCorrespondence.lean` and `Homological/Distance.lean`. -/

section Bridges

variable (L : ℕ) [Fact (0 < L)]

/-- The abstract `cutMap` of `toricHomologicalCode L` is the explicit
`toricVertexCutMap`.  Proof: both are the `𝔽₂`-transpose of `∂₁`, and
`∂₁` agrees on both definitions, so the transpose pairing
`∑ v, ∂₁(δ_e) v * s v = ∑ e', δ_e e' * cutMap s e'` isolates the value
at edge `e` on both sides. -/
theorem toricHomologicalCode_cutMap_eq :
    (toricHomologicalCode L).cutMap = δ⁰ (L := L) := by
  classical
  refine LinearMap.ext fun s => ?_
  funext e
  -- Use an explicit `if`-chain as the indicator of edge `e`; this is `Pi.single e 1`
  -- propositionally but avoids the family-inference complications of `Pi.single`.
  let δ : EdgeIdx L → ZMod 2 := fun e' => if e' = e then 1 else 0
  -- The abstract and toric transpose pairings, applied to `δ`.
  have h1 := (toricHomologicalCode L).boundary1_cutMap_transpose δ s
  have h2 := toricBoundary1_cutMap_transpose L δ s
  -- The δ-weighted sum over `f : EdgeIdx L → ZMod 2` is just `f e`.
  have hpi : ∀ f : EdgeIdx L → ZMod 2, ∑ e' : EdgeIdx L, δ e' * f e' = f e := by
    intro f
    have hsum :
        ∑ e' : EdgeIdx L, δ e' * f e' = δ e * f e := by
      refine Finset.sum_eq_single e ?_ ?_
      · intros e' _ hne
        change (if e' = e then (1 : ZMod 2) else 0) * f e' = 0
        rw [if_neg hne]; ring
      · intro h; exact absurd (Finset.mem_univ e) h
    rw [hsum]
    change (if e = e then (1 : ZMod 2) else 0) * f e = f e
    rw [if_pos rfl]; ring
  -- The two RHS sums are equal because the LHS sums are equal (both pair `∂₁ δ` with `s`).
  have hRHS :
      ∑ e' : EdgeIdx L, δ e' * (toricHomologicalCode L).cutMap s e'
      = ∑ e' : EdgeIdx L, δ e' * δ⁰ (L := L) s e' := by
    have hLHS_eq :
        ∑ v : VtxIdx L, (toricHomologicalCode L).boundary1 δ v * s v
        = ∑ v : VtxIdx L, ∂₁ (L := L) δ v * s v := rfl
    exact h1.symm.trans (hLHS_eq.trans h2)
  -- Specialize `hpi` to both maps and chain.
  have hL := hpi ((toricHomologicalCode L).cutMap s)
  have hR := hpi (δ⁰ (L := L) s)
  exact hL.symm.trans (hRHS.trans hR)

/-- The lattice `singleVtx v` is the abstract `singleVtx v`. -/
theorem toricHomologicalCode_singleVtx_eq (v : VtxIdx L) :
    (toricHomologicalCode L).singleVtx v = Lattice.singleVtx v := by
  change (Pi.single v 1 : VtxIdx L → ZMod 2) = fun u => if u = v then 1 else 0
  funext u
  simp [Pi.single_apply]

/-- The lattice `singleFace f` is the abstract `singleFace f`. -/
theorem toricHomologicalCode_singleFace_eq (f : FaceIdx L) :
    (toricHomologicalCode L).singleFace f = Lattice.singleFace f := by
  change (Pi.single f 1 : FaceIdx L → ZMod 2) = fun p => if p = f then 1 else 0
  funext p
  simp [Pi.single_apply]

variable [Fact (2 ≤ L)]

/-- Bridge: the abstract vertex stabilizer equals the lattice `vertexStab`. -/
theorem toricHomologicalCode_vertexStabOf_eq (v : VtxIdx L) :
    (toricHomologicalCode L).vertexStabOf v =
      StabilizerGroup.ToricCodeN.vertexStab L v.1 v.2 := by
  unfold Homological.HomologicalCode.vertexStabOf
  rw [toricHomologicalCode_chainZOperator_eq, toricHomologicalCode_cutMap_eq,
      toricHomologicalCode_singleVtx_eq]
  exact toricZOperatorOfChain_cutMap_singleVtx L v.1 v.2

/-- Bridge: the abstract face stabilizer equals the lattice `faceStab`.
    Routed through `toricXOperatorOfChain_boundary_singleFace`. -/
theorem toricHomologicalCode_faceStabOf_eq (f : FaceIdx L) :
    (toricHomologicalCode L).faceStabOf f =
      StabilizerGroup.ToricCodeN.faceStab L f.1 f.2 := by
  unfold Homological.HomologicalCode.faceStabOf
  rw [toricHomologicalCode_chainXOperator_eq, toricHomologicalCode_singleFace_eq]
  exact toricXOperatorOfChain_boundary_singleFace L f.1 f.2

/-- Bridge: the abstract Z-generator set equals the lattice `ZGenerators L`. -/
theorem toricHomologicalCode_ZGenerators_eq :
    (toricHomologicalCode L).ZGenerators = StabilizerGroup.ToricCodeN.ZGenerators L := by
  ext g
  refine ⟨?_, ?_⟩
  · rintro ⟨v, rfl⟩
    rw [toricHomologicalCode_vertexStabOf_eq]
    exact ⟨(v.1, v.2), rfl⟩
  · rintro ⟨⟨x, y⟩, rfl⟩
    refine ⟨(x, y), ?_⟩
    exact toricHomologicalCode_vertexStabOf_eq L (x, y)

/-- Bridge: the abstract X-generator set equals the lattice `XGenerators L`. -/
theorem toricHomologicalCode_XGenerators_eq :
    (toricHomologicalCode L).XGenerators = StabilizerGroup.ToricCodeN.XGenerators L := by
  ext g
  refine ⟨?_, ?_⟩
  · rintro ⟨f, rfl⟩
    rw [toricHomologicalCode_faceStabOf_eq]
    exact ⟨(f.1, f.2), rfl⟩
  · rintro ⟨⟨x, y⟩, rfl⟩
    refine ⟨(x, y), ?_⟩
    exact toricHomologicalCode_faceStabOf_eq L (x, y)

/-! Note: the `dual` bridges (`dualCycles_eq`, `dualBoundary_eq`,
`dualBoundaries_eq`) live in `ToricLogicalCorrespondenceZ.lean` — they reference
`toricDualBoundary`/`toricDualCycles`/`toricDualBoundaries`, which are defined
there.  See the §E.2 (Z-side) refactor for those bridges and the delegated iffs. -/

/-- Bridge: the lattice `StabilizerGroup.ToricCodeN.stabilizerGroup L` and the abstract
`(toricHomologicalCode L).homologicalStabilizerGroup` have the same underlying subgroup.

This is the key fact for delegating any `IsNontrivialLogicalOperator` /
`Subgroup`-mem statements between the toric and the generic stabilizer groups —
see `IsNontrivialLogicalOperator_of_toSubgroup_eq`. -/
theorem toricHomologicalCode_homologicalStabilizerGroup_toSubgroup_eq :
    (toricHomologicalCode L).homologicalStabilizerGroup.toSubgroup =
      (StabilizerGroup.ToricCodeN.stabilizerGroup L).toSubgroup := by
  rw [StabilizerGroup.ToricCodeN.stabilizerGroup_toSubgroup_eq]
  change Subgroup.closure (toricHomologicalCode L).homologicalGenerators =
    Subgroup.closure (StabilizerGroup.ToricCodeN.generators L)
  unfold Homological.HomologicalCode.homologicalGenerators
    StabilizerGroup.ToricCodeN.generators
  rw [toricHomologicalCode_ZGenerators_eq, toricHomologicalCode_XGenerators_eq]
  rfl

end Bridges

end Lattice
end Stabilizer
end Quantum
