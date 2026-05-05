import QEC.Stabilizer.Homological.LogicalCorrespondence
import QEC.Stabilizer.Core.CodeDistance

/-!
# §D — CSS distance bridge

For a homological CSS code, every Pauli element decomposes into an X-support
chain (qubits where it acts non-trivially with an X-component) and a Z-support
chain.  The key bridging fact is that for a non-trivial logical operator,
the X-chain and Z-chain *cannot* both be boundaries — otherwise we could build
a stabilizer with the same operators, contradicting non-triviality.

This file provides the abstract building blocks for distance arguments.
The full `code_distance_eq_min_dX_dZ` packaging is left to each instance
since `HasCodeDistance` requires a `StabilizerCode` (instance-specific).
-/

namespace Quantum
namespace Stabilizer
namespace Homological

open scoped BigOperators

namespace HomologicalCode

variable (X : HomologicalCode)

/-- Support of a 1-chain. -/
noncomputable def chainSupport (c : X.C1 → ZMod 2) : Finset X.C1 :=
  Finset.univ.filter (fun e => c e ≠ 0)

/-- Weight of a 1-chain (size of support). -/
noncomputable def chainWeight (c : X.C1 → ZMod 2) : ℕ := (X.chainSupport c).card

/-- X-support chain of a general Pauli (1 where the operator is X or Y). -/
noncomputable def xChainOf (g : NQubitPauliGroupElement X.numQubits) :
    X.C1 → ZMod 2 :=
  fun e =>
    if g.operators (X.edgeEquiv e) = PauliOperator.X ∨
       g.operators (X.edgeEquiv e) = PauliOperator.Y
    then 1 else 0

/-- Z-support chain of a general Pauli (1 where the operator is Z or Y). -/
noncomputable def zChainOf (g : NQubitPauliGroupElement X.numQubits) :
    X.C1 → ZMod 2 :=
  fun e =>
    if g.operators (X.edgeEquiv e) = PauliOperator.Z ∨
       g.operators (X.edgeEquiv e) = PauliOperator.Y
    then 1 else 0

variable {X}

/-- Helper: `ZMod 2` dichotomy (local copy). -/
private lemma zmod2_dichotomy_local (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hvalle : a.val ≤ 1 := Nat.le_of_lt_succ a.val_lt
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hvalle with h0 | h1
  · left
    calc a = ((a.val : ZMod 2)) := (ZMod.natCast_zmod_val a).symm
      _ = 0 := by simp [h0]
  · right
    calc a = ((a.val : ZMod 2)) := (ZMod.natCast_zmod_val a).symm
      _ = 1 := by simp [h1]

/-- The X-support chain extracted from `chainXOperator c` recovers `c`. -/
lemma xChainOf_chainXOperator (c : X.C1 → ZMod 2) :
    X.xChainOf (X.chainXOperator c) = c := by
  ext e
  simp only [xChainOf]
  by_cases h : c e = 1
  · have hex : ∃ e' : X.C1, X.edgeEquiv e' = X.edgeEquiv e ∧ c e' = 1 :=
      ⟨e, rfl, h⟩
    have h_op : (X.chainXOperator c).operators (X.edgeEquiv e) = PauliOperator.X := by
      rw [chainXOperator_op_at]
      exact if_pos hex
    rw [h_op]; simp [h]
  · have hnot : ¬ ∃ e' : X.C1, X.edgeEquiv e' = X.edgeEquiv e ∧ c e' = 1 := by
      rintro ⟨e', heq, he1⟩
      have he' : e' = e := X.edgeEquiv.injective heq
      exact h (he' ▸ he1)
    have h_op : (X.chainXOperator c).operators (X.edgeEquiv e) = PauliOperator.I := by
      rw [chainXOperator_op_at]
      exact if_neg hnot
    have h0 : c e = 0 := (zmod2_dichotomy_local (c e)).resolve_right h
    rw [h_op]; simp [h0]

/-! ## Weight bounds -/

/-- Weight of `g` is at least the edge-weight of its X-chain. -/
lemma weight_ge_chainWeight_xChainOf (g : NQubitPauliGroupElement X.numQubits) :
    NQubitPauliGroupElement.weight g ≥ X.chainWeight (X.xChainOf g) := by
  classical
  unfold NQubitPauliGroupElement.weight chainWeight chainSupport
  have himg :
      ((Finset.univ.filter (fun e : X.C1 => X.xChainOf g e ≠ 0)).image X.edgeEquiv) ⊆
        NQubitPauliOperator.support g.operators := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨e, he, rfl⟩
    have hne : X.xChainOf g e ≠ 0 := (Finset.mem_filter.mp he).2
    have h_op : g.operators (X.edgeEquiv e) = PauliOperator.X ∨
        g.operators (X.edgeEquiv e) = PauliOperator.Y := by
      by_contra hcontr
      push_neg at hcontr
      simp [xChainOf, hcontr.1, hcontr.2] at hne
    rcases h_op with hX | hY
    · simp [NQubitPauliOperator.support, hX]
    · simp [NQubitPauliOperator.support, hY]
  calc (NQubitPauliOperator.support g.operators).card
      ≥ ((Finset.univ.filter (fun e : X.C1 => X.xChainOf g e ≠ 0)).image X.edgeEquiv).card :=
        Finset.card_le_card himg
    _ = (Finset.univ.filter (fun e : X.C1 => X.xChainOf g e ≠ 0)).card :=
        Finset.card_image_of_injective _ X.edgeEquiv.injective

/-- Weight of `g` is at least the edge-weight of its Z-chain. -/
lemma weight_ge_chainWeight_zChainOf (g : NQubitPauliGroupElement X.numQubits) :
    NQubitPauliGroupElement.weight g ≥ X.chainWeight (X.zChainOf g) := by
  classical
  unfold NQubitPauliGroupElement.weight chainWeight chainSupport
  have himg :
      ((Finset.univ.filter (fun e : X.C1 => X.zChainOf g e ≠ 0)).image X.edgeEquiv) ⊆
        NQubitPauliOperator.support g.operators := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨e, he, rfl⟩
    have hne : X.zChainOf g e ≠ 0 := (Finset.mem_filter.mp he).2
    have h_op : g.operators (X.edgeEquiv e) = PauliOperator.Z ∨
        g.operators (X.edgeEquiv e) = PauliOperator.Y := by
      by_contra hcontr
      push_neg at hcontr
      simp [zChainOf, hcontr.1, hcontr.2] at hne
    rcases h_op with hZ | hY
    · simp [NQubitPauliOperator.support, hZ]
    · simp [NQubitPauliOperator.support, hY]
  calc (NQubitPauliOperator.support g.operators).card
      ≥ ((Finset.univ.filter (fun e : X.C1 => X.zChainOf g e ≠ 0)).image X.edgeEquiv).card :=
        Finset.card_le_card himg
    _ = (Finset.univ.filter (fun e : X.C1 => X.zChainOf g e ≠ 0)).card :=
        Finset.card_image_of_injective _ X.edgeEquiv.injective

/-! ## Operators of the X-only / Z-only encodings of a general Pauli -/

/-- The X-only encoding `chainXOperator (xChainOf g)` has X at qubits where g
acts as X or Y, and I elsewhere. -/
lemma chainXOperator_xChainOf_op_at
    (g : NQubitPauliGroupElement X.numQubits) (i : Fin X.numQubits) :
    (X.chainXOperator (X.xChainOf g)).operators i =
      (if g.operators i = PauliOperator.X ∨ g.operators i = PauliOperator.Y
       then PauliOperator.X else PauliOperator.I) := by
  classical
  rw [chainXOperator_op_at]
  by_cases hxy : g.operators i = PauliOperator.X ∨ g.operators i = PauliOperator.Y
  · -- some edge with i = eqv e and xChainOf = 1
    set e := X.edgeEquiv.symm i with he_def
    have hei : X.edgeEquiv e = i := by simp [he_def]
    have hx1 : X.xChainOf g e = 1 := by
      simp only [xChainOf]
      rw [hei]
      simp [hxy]
    have hex : ∃ e' : X.C1, X.edgeEquiv e' = i ∧ X.xChainOf g e' = 1 := ⟨e, hei, hx1⟩
    rw [if_pos hex, if_pos hxy]
  · push_neg at hxy
    have hex : ¬ ∃ e' : X.C1, X.edgeEquiv e' = i ∧ X.xChainOf g e' = 1 := by
      rintro ⟨e', hei, he1⟩
      have h0 : X.xChainOf g e' = 0 := by
        simp only [xChainOf]
        rw [hei]
        simp [hxy.1, hxy.2]
      rw [h0] at he1
      exact absurd he1 (by decide)
    rw [if_neg hex]
    rw [if_neg]
    push_neg
    exact hxy

/-- Z-only mirror. -/
lemma chainZOperator_zChainOf_op_at
    (g : NQubitPauliGroupElement X.numQubits) (i : Fin X.numQubits) :
    (X.chainZOperator (X.zChainOf g)).operators i =
      (if g.operators i = PauliOperator.Z ∨ g.operators i = PauliOperator.Y
       then PauliOperator.Z else PauliOperator.I) := by
  classical
  rw [chainZOperator_op_at]
  by_cases hzy : g.operators i = PauliOperator.Z ∨ g.operators i = PauliOperator.Y
  · set e := X.edgeEquiv.symm i with he_def
    have hei : X.edgeEquiv e = i := by simp [he_def]
    have hz1 : X.zChainOf g e = 1 := by
      simp only [zChainOf]
      rw [hei]
      simp [hzy]
    have hex : ∃ e' : X.C1, X.edgeEquiv e' = i ∧ X.zChainOf g e' = 1 := ⟨e, hei, hz1⟩
    rw [if_pos hex, if_pos hzy]
  · push_neg at hzy
    have hex : ¬ ∃ e' : X.C1, X.edgeEquiv e' = i ∧ X.zChainOf g e' = 1 := by
      rintro ⟨e', hei, he1⟩
      have h0 : X.zChainOf g e' = 0 := by
        simp only [zChainOf]
        rw [hei]
        simp [hzy.1, hzy.2]
      rw [h0] at he1
      exact absurd he1 (by decide)
    rw [if_neg hex]
    rw [if_neg]
    push_neg
    exact hzy

/-! ## not_both_boundary_of_nontrivial

Note: the Z-side closure helpers (`chainZOperator_cutMap_mem_ZClosure`,
`chainZOperator_mem_ZClosure_of_mem_dualBoundaries`) live alongside their X-side
mirrors in `LogicalCorrespondence.lean`.
-/

/-- Helper: combining the X-only and Z-only encodings of `g` (their operator part)
recovers `g.operators` qubit-by-qubit. -/
private lemma chainOps_xz_combine_eq
    (g : NQubitPauliGroupElement X.numQubits) (i : Fin X.numQubits) :
    (((X.chainXOperator (X.xChainOf g)).operators i).mulOp
        ((X.chainZOperator (X.zChainOf g)).operators i)).operator =
      g.operators i := by
  rw [chainXOperator_xChainOf_op_at, chainZOperator_zChainOf_op_at]
  cases hgi : g.operators i <;> simp [PauliOperator.mulOp]

/-- For a nontrivial logical operator, the X-chain and Z-chain cannot both be
in the respective boundaries (CSS bridge). -/
theorem not_both_boundary_of_nontrivial
    (g : NQubitPauliGroupElement X.numQubits)
    (hg : Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
            X.homologicalStabilizerGroup) :
    ¬ (X.xChainOf g ∈ X.boundaries ∧ X.zChainOf g ∈ X.dualBoundaries) := by
  classical
  rintro ⟨hxBnd, hzBnd⟩
  set g_X := X.chainXOperator (X.xChainOf g) with hg_X
  set g_Z := X.chainZOperator (X.zChainOf g) with hg_Z
  -- g_X ∈ stabilizer (via X-closure ⊆ Z∪X-closure)
  have hgX_mem : g_X ∈ X.homologicalStabilizerGroup.toSubgroup := by
    have hXcl : g_X ∈ Subgroup.closure X.XGenerators :=
      (chainXOperator_mem_XClosure_iff_mem_boundaries (X.xChainOf g)).mpr hxBnd
    have : Subgroup.closure X.XGenerators ≤
        Subgroup.closure (X.ZGenerators ∪ X.XGenerators) :=
      Subgroup.closure_mono (Set.subset_union_right)
    exact this hXcl
  -- g_Z ∈ stabilizer (similarly)
  have hgZ_mem : g_Z ∈ X.homologicalStabilizerGroup.toSubgroup := by
    have hZcl : g_Z ∈ Subgroup.closure X.ZGenerators :=
      chainZOperator_mem_ZClosure_of_mem_dualBoundaries (X.zChainOf g) hzBnd
    have : Subgroup.closure X.ZGenerators ≤
        Subgroup.closure (X.ZGenerators ∪ X.XGenerators) :=
      Subgroup.closure_mono (Set.subset_union_left)
    exact this hZcl
  have hprod_mem : g_X * g_Z ∈ X.homologicalStabilizerGroup.toSubgroup :=
    X.homologicalStabilizerGroup.toSubgroup.mul_mem hgX_mem hgZ_mem
  -- Operators of g_X * g_Z match g.operators qubitwise.
  have hops_eq : (g_X * g_Z).operators = g.operators := by
    ext i
    show ((g_X.operators i).mulOp (g_Z.operators i)).operator = g.operators i
    exact chainOps_xz_combine_eq g i
  -- Use the third condition of IsNontrivialLogicalOperator
  rw [Quantum.StabilizerGroup.IsNontrivialLogicalOperator_iff] at hg
  obtain ⟨_, _, h_no_phase_dup⟩ := hg
  exact h_no_phase_dup (g_X * g_Z) hprod_mem hops_eq

end HomologicalCode

end Homological
end Stabilizer
end Quantum
