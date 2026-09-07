import QEC.Stabilizer.Framework.Homological.LogicalCorrespondence
import QEC.Stabilizer.Framework.Core.Logical.CodeDistance

/-!
# §D — CSS distance bridge

For a homological CSS code, every Pauli element decomposes into an X-support
chain (qubits where it acts non-trivially with an X-component) and a Z-support
chain. The key bridging fact is that for a non-trivial logical operator, the
X-chain and Z-chain *cannot* both be boundaries — otherwise we could build a
stabilizer with the same operators, contradicting non-triviality.

This file provides the abstract building blocks for distance arguments. The full
`code_distance_eq_min_dX_dZ` packaging is left to each instance since
`HasCodeDistance` requires a `StabilizerCode` (instance-specific).
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
      push Not at hcontr
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
      push Not at hcontr
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
  · push Not at hxy
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
    push Not
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
  · push Not at hzy
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
    push Not
    exact hzy

/-! ## Weight of the X- / Z-only encodings

The qubit support of `chainXOperator c` (resp. `chainZOperator c`) is in
bijection with `chainSupport c` via `edgeEquiv`, hence the operator weight
equals the chain weight. -/

/-- `weight (chainXOperator c) = chainWeight c`. -/
lemma weight_chainXOperator (c : X.C1 → ZMod 2) :
    NQubitPauliGroupElement.weight (X.chainXOperator c) = X.chainWeight c := by
  classical
  unfold NQubitPauliGroupElement.weight NQubitPauliOperator.weight
    chainWeight chainSupport
  symm
  apply Finset.card_bij (fun v _ => X.edgeEquiv v)
  · intro v hv
    rw [Finset.mem_filter] at hv
    have h1 : c v = 1 :=
      (zmod2_dichotomy_local (c v)).resolve_left hv.2
    exact (mem_support_chainXOperator_iff c v).mpr h1
  · intros v₁ _ v₂ _ heq
    exact X.edgeEquiv.injective heq
  · intros q hq
    refine ⟨X.edgeEquiv.symm q, ?_, by simp⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h_iff := mem_support_chainXOperator_iff (X := X) c (X.edgeEquiv.symm q)
    rw [Equiv.apply_symm_apply] at h_iff
    have : c (X.edgeEquiv.symm q) = 1 := h_iff.mp hq
    rw [this]; decide

/-- Mirror: `weight (chainZOperator c) = chainWeight c`. -/
lemma weight_chainZOperator (c : X.C1 → ZMod 2) :
    NQubitPauliGroupElement.weight (X.chainZOperator c) = X.chainWeight c := by
  classical
  unfold NQubitPauliGroupElement.weight NQubitPauliOperator.weight
    chainWeight chainSupport
  symm
  apply Finset.card_bij (fun v _ => X.edgeEquiv v)
  · intro v hv
    rw [Finset.mem_filter] at hv
    have h1 : c v = 1 :=
      (zmod2_dichotomy_local (c v)).resolve_left hv.2
    exact (mem_support_chainZOperator_iff c v).mpr h1
  · intros v₁ _ v₂ _ heq
    exact X.edgeEquiv.injective heq
  · intros q hq
    refine ⟨X.edgeEquiv.symm q, ?_, by simp⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h_iff := mem_support_chainZOperator_iff (X := X) c (X.edgeEquiv.symm q)
    rw [Equiv.apply_symm_apply] at h_iff
    have : c (X.edgeEquiv.symm q) = 1 := h_iff.mp hq
    rw [this]; decide

/-! ## Qubit-wise anticommutation bridges

For any qubit `i`, the qubit-wise anticommutation of `g` against a Z-type
generator (`vertexStabOf v`) is determined entirely by `g`'s X-content at `i`,
i.e. matches that of `chainXOperator (xChainOf g)`. Mirror on the Z side. These
let centralizer-style arguments on `g` transfer to its X-only / Z-only encoding
without redoing the Pauli case analysis. -/

/-- Anticommutation against the Z-type vertex stab matches between `g` and its
X-only encoding `chainXOperator (xChainOf g)`. -/
lemma anticommutesAt_vertexStabOf_iff_xChainOf
    (g : NQubitPauliGroupElement X.numQubits) (v : X.C0)
    (i : Fin X.numQubits) :
    NQubitPauliGroupElement.anticommutesAt (X.vertexStabOf v).operators
        g.operators i ↔
      NQubitPauliGroupElement.anticommutesAt (X.vertexStabOf v).operators
        (X.chainXOperator (X.xChainOf g)).operators i := by
  have hZ : (X.vertexStabOf v).operators i = PauliOperator.I ∨
      (X.vertexStabOf v).operators i = PauliOperator.Z :=
    (vertexStabOf_isZType v).2 i
  have heq := chainXOperator_xChainOf_op_at (X := X) g i
  rcases hZ with hI | hZ
  · simp only [NQubitPauliGroupElement.anticommutesAt, hI]
    cases hgi : g.operators i <;>
      cases hxi : (X.chainXOperator (X.xChainOf g)).operators i <;>
      simp [PauliOperator.mulOp]
  · simp only [NQubitPauliGroupElement.anticommutesAt, hZ, heq]
    cases hgi : g.operators i <;>
      simp [PauliOperator.mulOp]

/-- Mirror: anticommutation against the X-type face stab matches between `g` and
its Z-only encoding `chainZOperator (zChainOf g)`. -/
lemma anticommutesAt_faceStabOf_iff_zChainOf
    (g : NQubitPauliGroupElement X.numQubits) (f : X.C2)
    (i : Fin X.numQubits) :
    NQubitPauliGroupElement.anticommutesAt (X.faceStabOf f).operators
        g.operators i ↔
      NQubitPauliGroupElement.anticommutesAt (X.faceStabOf f).operators
        (X.chainZOperator (X.zChainOf g)).operators i := by
  have hX : (X.faceStabOf f).operators i = PauliOperator.I ∨
      (X.faceStabOf f).operators i = PauliOperator.X :=
    (faceStabOf_isXType f).2 i
  have heq := chainZOperator_zChainOf_op_at (X := X) g i
  rcases hX with hI | hX
  · simp only [NQubitPauliGroupElement.anticommutesAt, hI]
    cases hgi : g.operators i <;>
      cases hzi : (X.chainZOperator (X.zChainOf g)).operators i <;>
      simp [PauliOperator.mulOp]
  · simp only [NQubitPauliGroupElement.anticommutesAt, hX, heq]
    cases hgi : g.operators i <;>
      simp [PauliOperator.mulOp]

/-! ## Centralizer → cycle bridges

These complete the qubit-level commutation story: if `g` commutes with every
stabilizer, then its X-chain is a 1-cycle (resp. Z-chain is a dual 1-cycle). The
bridge runs through `chainXOperator_mem_centralizer_iff_mem_cycles` from
`LogicalCorrespondence.lean`. -/

/-- For `g ∈ centralizer`, `xChainOf g` is a 1-cycle. -/
lemma xChainOf_mem_cycles_of_centralizer
    (g : NQubitPauliGroupElement X.numQubits)
    (hg : g ∈ Quantum.StabilizerGroup.centralizer X.homologicalStabilizerGroup) :
    X.xChainOf g ∈ X.cycles := by
  apply (chainXOperator_mem_centralizer_iff_mem_cycles (X.xChainOf g)).mp
  intro s hs
  refine Subgroup.closure_induction
    (p := fun y _ => y * X.chainXOperator (X.xChainOf g) =
      X.chainXOperator (X.xChainOf g) * y) ?_ ?_ ?_ ?_ hs
  · rintro y (⟨v, rfl⟩ | ⟨f, rfl⟩)
    · -- y = vertexStabOf v (Z-type generator)
      have hmem : X.vertexStabOf v ∈ X.homologicalStabilizerGroup.toSubgroup :=
        Subgroup.subset_closure (Or.inl ⟨v, rfl⟩)
      have hcomm_g : X.vertexStabOf v * g = g * X.vertexStabOf v :=
        (Quantum.StabilizerGroup.mem_centralizer_iff g _).mp hg _ hmem
      rw [NQubitPauliGroupElement.commutes_iff_even_anticommutes] at hcomm_g ⊢
      classical
      have hfilter_eq :
          Finset.univ.filter (NQubitPauliGroupElement.anticommutesAt
              (X.vertexStabOf v).operators
              (X.chainXOperator (X.xChainOf g)).operators) =
            Finset.univ.filter (NQubitPauliGroupElement.anticommutesAt
              (X.vertexStabOf v).operators g.operators) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (anticommutesAt_vertexStabOf_iff_xChainOf (X := X) g v i).symm
      rw [hfilter_eq]
      exact hcomm_g
    · -- y = faceStabOf f (X-type generator) — X-X commutes
      exact chainXOperator_commutes_faceStabOf (X := X) (X.xChainOf g) f
  · change (1 : NQubitPauliGroupElement X.numQubits) *
        X.chainXOperator (X.xChainOf g) =
        X.chainXOperator (X.xChainOf g) * 1
    rw [_root_.one_mul, _root_.mul_one]
  · intros y₁ y₂ _ _ hy₁ hy₂
    calc (y₁ * y₂) * X.chainXOperator (X.xChainOf g)
        = y₁ * (y₂ * X.chainXOperator (X.xChainOf g)) := _root_.mul_assoc _ _ _
      _ = y₁ * (X.chainXOperator (X.xChainOf g) * y₂) := by rw [hy₂]
      _ = (y₁ * X.chainXOperator (X.xChainOf g)) * y₂ := (_root_.mul_assoc _ _ _).symm
      _ = (X.chainXOperator (X.xChainOf g) * y₁) * y₂ := by rw [hy₁]
      _ = X.chainXOperator (X.xChainOf g) * (y₁ * y₂) := _root_.mul_assoc _ _ _
  · intros y _ hy
    exact (show Commute y _ from hy).inv_left.eq

/-- Mirror: for `g ∈ centralizer`, `zChainOf g` is a dual 1-cycle. -/
lemma zChainOf_mem_dualCycles_of_centralizer
    (g : NQubitPauliGroupElement X.numQubits)
    (hg : g ∈ Quantum.StabilizerGroup.centralizer X.homologicalStabilizerGroup) :
    X.zChainOf g ∈ X.dualCycles := by
  apply (chainZOperator_mem_centralizer_iff_mem_dualCycles (X.zChainOf g)).mp
  intro s hs
  refine Subgroup.closure_induction
    (p := fun y _ => y * X.chainZOperator (X.zChainOf g) =
      X.chainZOperator (X.zChainOf g) * y) ?_ ?_ ?_ ?_ hs
  · rintro y (⟨v, rfl⟩ | ⟨f, rfl⟩)
    · -- y = vertexStabOf v (Z-type generator) — Z-Z commutes
      exact chainZOperator_commutes_vertexStabOf (X := X) (X.zChainOf g) v
    · -- y = faceStabOf f (X-type generator)
      have hmem : X.faceStabOf f ∈ X.homologicalStabilizerGroup.toSubgroup :=
        Subgroup.subset_closure (Or.inr ⟨f, rfl⟩)
      have hcomm_g : X.faceStabOf f * g = g * X.faceStabOf f :=
        (Quantum.StabilizerGroup.mem_centralizer_iff g _).mp hg _ hmem
      rw [NQubitPauliGroupElement.commutes_iff_even_anticommutes] at hcomm_g ⊢
      classical
      have hfilter_eq :
          Finset.univ.filter (NQubitPauliGroupElement.anticommutesAt
              (X.faceStabOf f).operators
              (X.chainZOperator (X.zChainOf g)).operators) =
            Finset.univ.filter (NQubitPauliGroupElement.anticommutesAt
              (X.faceStabOf f).operators g.operators) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (anticommutesAt_faceStabOf_iff_zChainOf (X := X) g f i).symm
      rw [hfilter_eq]
      exact hcomm_g
  · change (1 : NQubitPauliGroupElement X.numQubits) *
        X.chainZOperator (X.zChainOf g) =
        X.chainZOperator (X.zChainOf g) * 1
    rw [_root_.one_mul, _root_.mul_one]
  · intros y₁ y₂ _ _ hy₁ hy₂
    calc (y₁ * y₂) * X.chainZOperator (X.zChainOf g)
        = y₁ * (y₂ * X.chainZOperator (X.zChainOf g)) := _root_.mul_assoc _ _ _
      _ = y₁ * (X.chainZOperator (X.zChainOf g) * y₂) := by rw [hy₂]
      _ = (y₁ * X.chainZOperator (X.zChainOf g)) * y₂ := (_root_.mul_assoc _ _ _).symm
      _ = (X.chainZOperator (X.zChainOf g) * y₁) * y₂ := by rw [hy₁]
      _ = X.chainZOperator (X.zChainOf g) * (y₁ * y₂) := _root_.mul_assoc _ _ _
  · intros y _ hy
    exact (show Commute y _ from hy).inv_left.eq

/-! ## not_both_boundary_of_nontrivial

Note: the Z-side closure helpers (`chainZOperator_cutMap_mem_ZClosure`,
`chainZOperator_mem_ZClosure_of_mem_dualBoundaries`) live alongside their X-side
mirrors in `LogicalCorrespondence.lean`.
-/

/-- Helper: combining the X-only and Z-only encodings of `g` (their operator
part) recovers `g.operators` qubit-by-qubit. -/
private lemma chainOps_xz_combine_eq
    (g : NQubitPauliGroupElement X.numQubits) (i : Fin X.numQubits) :
    (((X.chainXOperator (X.xChainOf g)).operators i).mulOp
        ((X.chainZOperator (X.zChainOf g)).operators i)).operator =
      g.operators i := by
  rw [chainXOperator_xChainOf_op_at, chainZOperator_zChainOf_op_at]
  cases hgi : g.operators i <;> simp [PauliOperator.mulOp]

/-- For a nontrivial logical operator, the X-chain and Z-chain cannot both be in
the respective boundaries (CSS bridge). -/
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
    change ((g_X.operators i).mulOp (g_Z.operators i)).operator = g.operators i
    exact chainOps_xz_combine_eq g i
  -- Use the third condition of IsNontrivialLogicalOperator
  rw [Quantum.StabilizerGroup.IsNontrivialLogicalOperator_iff] at hg
  obtain ⟨_, _, h_no_phase_dup⟩ := hg
  exact h_no_phase_dup (g_X * g_Z) hprod_mem hops_eq

/-! ## Chain-weight → Pauli-weight distance bridge (combinator)

Packages the abstract CSS bridge into a single statement that downstream
homological-code distance proofs can call directly. Given lower bounds on
non-boundary X-cycles' chain weight (`hX`) and non-dual-boundary Z-cycles' chain
weight (`hZ`), every non-trivial logical Pauli has weight ≥ the respective
bound.

Combines:
- `xChainOf_mem_cycles_of_centralizer` /
  `zChainOf_mem_dualCycles_of_centralizer`
- `not_both_boundary_of_nontrivial`
- `weight_ge_chainWeight_xChainOf` / `weight_ge_chainWeight_zChainOf`

This is the natural CSS-bridge entry point for new code families with parametric
chain-weight bounds (BB codes, hypergraph products, etc.). The existing
rotated-surface and toric distance proofs predate this combinator and inline the
case-split; they could be refactored to use this directly, but that's left as a
future cleanup. -/

/-- Symmetric form: a single lower bound `K` on both X- and Z-cycle chain
weights yields a lower bound on every non-trivial logical's Pauli weight. -/
theorem chainWeight_lower_bound_transfers
    (X : HomologicalCode) (K : ℕ)
    (hX : ∀ c ∈ X.cycles, c ∉ X.boundaries → K ≤ X.chainWeight c)
    (hZ : ∀ c ∈ X.dualCycles, c ∉ X.dualBoundaries → K ≤ X.chainWeight c)
    (g : NQubitPauliGroupElement X.numQubits)
    (hg : Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
            X.homologicalStabilizerGroup) :
    K ≤ NQubitPauliGroupElement.weight g := by
  have hg_centralizer : g ∈ Quantum.StabilizerGroup.centralizer
      X.homologicalStabilizerGroup := by
    rw [Quantum.StabilizerGroup.IsNontrivialLogicalOperator_iff] at hg
    exact hg.1
  have hxCyc : X.xChainOf g ∈ X.cycles :=
    xChainOf_mem_cycles_of_centralizer g hg_centralizer
  have hzCyc : X.zChainOf g ∈ X.dualCycles :=
    zChainOf_mem_dualCycles_of_centralizer g hg_centralizer
  have hnot_both := not_both_boundary_of_nontrivial g hg
  rcases Classical.em (X.xChainOf g ∈ X.boundaries) with hxBnd | hxNotBnd
  · have hzNotBnd : X.zChainOf g ∉ X.dualBoundaries := by
      intro hzBnd
      exact hnot_both ⟨hxBnd, hzBnd⟩
    exact (hZ _ hzCyc hzNotBnd).trans (weight_ge_chainWeight_zChainOf g)
  · exact (hX _ hxCyc hxNotBnd).trans (weight_ge_chainWeight_xChainOf g)

/-- Asymmetric form: separate `K_X` and `K_Z` lower bounds, conclusion uses
`min K_X K_Z`. Useful when the two sides of a CSS code have genuinely different
chain-weight bounds. -/
theorem chainWeight_lower_bound_transfers_asymmetric
    (X : HomologicalCode) (K_X K_Z : ℕ)
    (hX : ∀ c ∈ X.cycles, c ∉ X.boundaries → K_X ≤ X.chainWeight c)
    (hZ : ∀ c ∈ X.dualCycles, c ∉ X.dualBoundaries → K_Z ≤ X.chainWeight c)
    (g : NQubitPauliGroupElement X.numQubits)
    (hg : Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
            X.homologicalStabilizerGroup) :
    min K_X K_Z ≤ NQubitPauliGroupElement.weight g := by
  have hX' : ∀ c ∈ X.cycles, c ∉ X.boundaries →
      min K_X K_Z ≤ X.chainWeight c := fun c hc hnb =>
    (min_le_left _ _).trans (hX c hc hnb)
  have hZ' : ∀ c ∈ X.dualCycles, c ∉ X.dualBoundaries →
      min K_X K_Z ≤ X.chainWeight c := fun c hc hnb =>
    (min_le_right _ _).trans (hZ c hc hnb)
  exact chainWeight_lower_bound_transfers X _ hX' hZ' g hg

end HomologicalCode

end Homological
end Stabilizer
end Quantum
