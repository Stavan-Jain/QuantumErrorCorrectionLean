import Mathlib.Tactic
import QEC.Stabilizer.Codes.ToricCodeNDistanceX
import QEC.Stabilizer.Codes.ToricCodeNDistanceZ
import QEC.Stabilizer.Codes.ToricCodeNStabilizerCode
import QEC.Stabilizer.Lattice.ToricLogicalCorrespondenceZ
import QEC.Stabilizer.PauliGroup.NQubitElement
import QEC.Stabilizer.Core.CodeDistance

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
-- 1.  CSS bridge: full distance = min(dX, dZ)
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
  have hL0 : 0 < L := Nat.lt_of_lt_of_le (by decide : 0 < 2) (Fact.out : 2 ≤ L)
  haveI : Fact (0 < L) := ⟨hL0⟩
  unfold weight Stabilizer.Lattice.edgeWeight
  classical
  have himg :
      (Stabilizer.Lattice.edgeSupport (L := L) (xChainOf L g)).image
        (Stabilizer.Lattice.edgeToQubitIdx L) ⊆
        NQubitPauliOperator.support g.operators := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨e, he, rfl⟩
    have hne : xChainOf L g e ≠ 0 := (Stabilizer.Lattice.mem_edgeSupport _ _).mp he
    have : g.operators (Stabilizer.Lattice.edgeToQubitIdx L e) = PauliOperator.X ∨
        g.operators (Stabilizer.Lattice.edgeToQubitIdx L e) = PauliOperator.Y := by
      by_contra h
      push_neg at h
      simp [xChainOf, h.1, h.2] at hne
    rcases this with hX | hY
    · simp [NQubitPauliOperator.support, hX]
    · simp [NQubitPauliOperator.support, hY]
  calc (NQubitPauliOperator.support g.operators).card
      ≥ ((Stabilizer.Lattice.edgeSupport (L := L) (xChainOf L g)).image
          (Stabilizer.Lattice.edgeToQubitIdx L)).card :=
        Finset.card_le_card himg
    _ = (Stabilizer.Lattice.edgeSupport (L := L) (xChainOf L g)).card := by
        rw [Finset.card_image_of_injective _ (Stabilizer.Lattice.edgeToQubitIdx_injective L)]

/-- Weight of `g` is at least the edge-weight of its Z-chain. -/
private lemma weight_ge_edgeWeight_zChain (L : ℕ) [Fact (2 ≤ L)]
    (g : NQubitPauliGroupElement (numQubits L)) :
    weight g ≥ Stabilizer.Lattice.edgeWeight (L := L) (zChainOf L g) := by
  have hL0 : 0 < L := Nat.lt_of_lt_of_le (by decide : 0 < 2) (Fact.out : 2 ≤ L)
  haveI : Fact (0 < L) := ⟨hL0⟩
  unfold weight Stabilizer.Lattice.edgeWeight
  classical
  have himg :
      (Stabilizer.Lattice.edgeSupport (L := L) (zChainOf L g)).image
        (Stabilizer.Lattice.edgeToQubitIdx L) ⊆
        NQubitPauliOperator.support g.operators := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨e, he, rfl⟩
    have hne : zChainOf L g e ≠ 0 := (Stabilizer.Lattice.mem_edgeSupport _ _).mp he
    have : g.operators (Stabilizer.Lattice.edgeToQubitIdx L e) = PauliOperator.Z ∨
        g.operators (Stabilizer.Lattice.edgeToQubitIdx L e) = PauliOperator.Y := by
      by_contra h
      push_neg at h
      simp [zChainOf, h.1, h.2] at hne
    rcases this with hZ | hY
    · simp [NQubitPauliOperator.support, hZ]
    · simp [NQubitPauliOperator.support, hY]
  calc (NQubitPauliOperator.support g.operators).card
      ≥ ((Stabilizer.Lattice.edgeSupport (L := L) (zChainOf L g)).image
          (Stabilizer.Lattice.edgeToQubitIdx L)).card :=
        Finset.card_le_card himg
    _ = (Stabilizer.Lattice.edgeSupport (L := L) (zChainOf L g)).card := by
        rw [Finset.card_image_of_injective _ (Stabilizer.Lattice.edgeToQubitIdx_injective L)]

/-- `edgeToQubitIdx` is surjective (since it is injective between equinumerous types). -/
private lemma edgeToQubitIdx_surjective (L : ℕ) [Fact (0 < L)] :
    Function.Surjective (Stabilizer.Lattice.edgeToQubitIdx L) := by
  classical
  have hcard_edge : Fintype.card (Stabilizer.Lattice.EdgeIdx L) =
      Fintype.card (Fin (Stabilizer.Lattice.toricNumQubits L)) := by
    simp [Stabilizer.Lattice.toricNumQubits, two_mul, mul_comm]
  exact (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨Stabilizer.Lattice.edgeToQubitIdx_injective L, hcard_edge⟩ |>.2

/-- The X-only encoding `toricXOperatorOfChain (xChainOf g)` has, at each qubit, an X
exactly when `g` has X or Y. -/
private lemma toricXOf_xChain_operators_eq (L : ℕ) [Fact (0 < L)]
    (g : NQubitPauliGroupElement (numQubits L)) (i : Fin (numQubits L)) :
    (Stabilizer.Lattice.toricXOperatorOfChain L (xChainOf L g)).operators i =
      (if g.operators i = PauliOperator.X ∨ g.operators i = PauliOperator.Y
       then PauliOperator.X else PauliOperator.I) := by
  classical
  by_cases hxy : g.operators i = PauliOperator.X ∨ g.operators i = PauliOperator.Y
  · obtain ⟨e, hei⟩ := edgeToQubitIdx_surjective L i
    have he1 : xChainOf L g e = 1 := by
      rcases hxy with hX | hY
      · simp [xChainOf, hei, hX]
      · simp [xChainOf, hei, hY]
    have hex : ∃ e : Stabilizer.Lattice.EdgeIdx L,
        Stabilizer.Lattice.edgeToQubitIdx L e = i ∧ xChainOf L g e = 1 := ⟨e, hei, he1⟩
    simp [Stabilizer.Lattice.toricXOperatorOfChain, hex, hxy]
  · push_neg at hxy
    have hex : ¬ ∃ e : Stabilizer.Lattice.EdgeIdx L,
        Stabilizer.Lattice.edgeToQubitIdx L e = i ∧ xChainOf L g e = 1 := by
      rintro ⟨e, hei, he1⟩
      have h_xchain_zero : xChainOf L g e = 0 := by
        subst hei; simp [xChainOf, hxy.1, hxy.2]
      rw [h_xchain_zero] at he1
      exact absurd he1 (by decide)
    simp [Stabilizer.Lattice.toricXOperatorOfChain, hex, hxy]

/-- For each qubit, anticommutation between `vertexStab` (Z-type) and a general `g` is
equivalent to anticommutation between `vertexStab` and the X-only encoding of `xChainOf g`. -/
private lemma anticommutesAt_vertexStab_g_iff_xChain
    (L : ℕ) [Fact (2 ≤ L)] (g : NQubitPauliGroupElement (numQubits L))
    (xv yv : Fin L) (i : Fin (numQubits L)) :
    NQubitPauliGroupElement.anticommutesAt
        (vertexStab L xv yv).operators g.operators i ↔
      NQubitPauliGroupElement.anticommutesAt
        (vertexStab L xv yv).operators
        (Stabilizer.Lattice.toricXOperatorOfChain L (xChainOf L g)).operators i := by
  have hL0 : 0 < L := Nat.lt_of_lt_of_le (by decide : 0 < 2) (Fact.out : 2 ≤ L)
  haveI : Fact (0 < L) := ⟨hL0⟩
  have hZ : (vertexStab L xv yv).operators i = PauliOperator.I ∨
      (vertexStab L xv yv).operators i = PauliOperator.Z :=
    (vertexStab_is_ZType L xv yv).2 i
  have heq := toricXOf_xChain_operators_eq L g i
  rcases hZ with hI | hZ
  · simp only [NQubitPauliGroupElement.anticommutesAt, hI]
    cases hgi : g.operators i <;>
      cases hxi : (Stabilizer.Lattice.toricXOperatorOfChain L (xChainOf L g)).operators i <;>
      simp [PauliOperator.mulOp]
  · simp only [NQubitPauliGroupElement.anticommutesAt, hZ, heq]
    cases hgi : g.operators i <;>
      simp [PauliOperator.mulOp, hgi]

/-- The Z-only encoding `toricZOperatorOfChain (zChainOf g)` has, at each qubit, a Z
exactly when `g` has Z or Y. -/
private lemma toricZOf_zChain_operators_eq (L : ℕ) [Fact (0 < L)]
    (g : NQubitPauliGroupElement (numQubits L)) (i : Fin (numQubits L)) :
    (Stabilizer.Lattice.toricZOperatorOfChain L (zChainOf L g)).operators i =
      (if g.operators i = PauliOperator.Z ∨ g.operators i = PauliOperator.Y
       then PauliOperator.Z else PauliOperator.I) := by
  classical
  by_cases hzy : g.operators i = PauliOperator.Z ∨ g.operators i = PauliOperator.Y
  · obtain ⟨e, hei⟩ := edgeToQubitIdx_surjective L i
    have he1 : zChainOf L g e = 1 := by
      rcases hzy with hZ | hY
      · simp [zChainOf, hei, hZ]
      · simp [zChainOf, hei, hY]
    have hex : ∃ e : Stabilizer.Lattice.EdgeIdx L,
        Stabilizer.Lattice.edgeToQubitIdx L e = i ∧ zChainOf L g e = 1 := ⟨e, hei, he1⟩
    simp [Stabilizer.Lattice.toricZOperatorOfChain, hex, hzy]
  · push_neg at hzy
    have hex : ¬ ∃ e : Stabilizer.Lattice.EdgeIdx L,
        Stabilizer.Lattice.edgeToQubitIdx L e = i ∧ zChainOf L g e = 1 := by
      rintro ⟨e, hei, he1⟩
      have h_zchain_zero : zChainOf L g e = 0 := by
        subst hei; simp [zChainOf, hzy.1, hzy.2]
      rw [h_zchain_zero] at he1
      exact absurd he1 (by decide)
    simp [Stabilizer.Lattice.toricZOperatorOfChain, hex, hzy]

/-- For each qubit, anticommutation between `faceStab` (X-type) and a general `g` is
equivalent to anticommutation between `faceStab` and the Z-only encoding of `zChainOf g`. -/
private lemma anticommutesAt_faceStab_g_iff_zChain
    (L : ℕ) [Fact (2 ≤ L)] (g : NQubitPauliGroupElement (numQubits L))
    (xf yf : Fin L) (i : Fin (numQubits L)) :
    NQubitPauliGroupElement.anticommutesAt
        (faceStab L xf yf).operators g.operators i ↔
      NQubitPauliGroupElement.anticommutesAt
        (faceStab L xf yf).operators
        (Stabilizer.Lattice.toricZOperatorOfChain L (zChainOf L g)).operators i := by
  have hL0 : 0 < L := Nat.lt_of_lt_of_le (by decide : 0 < 2) (Fact.out : 2 ≤ L)
  haveI : Fact (0 < L) := ⟨hL0⟩
  have hX : (faceStab L xf yf).operators i = PauliOperator.I ∨
      (faceStab L xf yf).operators i = PauliOperator.X :=
    (faceStab_is_XType L xf yf).2 i
  have heq := toricZOf_zChain_operators_eq L g i
  rcases hX with hI | hX
  · simp only [NQubitPauliGroupElement.anticommutesAt, hI]
    cases hgi : g.operators i <;>
      cases hzi : (Stabilizer.Lattice.toricZOperatorOfChain L (zChainOf L g)).operators i <;>
      simp [PauliOperator.mulOp]
  · simp only [NQubitPauliGroupElement.anticommutesAt, hX, heq]
    cases hgi : g.operators i <;>
      simp [PauliOperator.mulOp, hgi]

/-- If `g` is in the centralizer, its X-chain is a primal cycle. -/
private lemma xChain_mem_toricCycles_of_centralizer (L : ℕ) [Fact (2 ≤ L)]
    (g : NQubitPauliGroupElement (numQubits L))
    (hg : g ∈ centralizer (stabilizerGroup L)) :
    xChainOf L g ∈ Stabilizer.Lattice.toricCycles (L := L) := by
  apply (Stabilizer.Lattice.xCommutesWithZChecks_iff_mem_toricCycles L (xChainOf L g)).mp
  intro z hz
  rcases hz with ⟨⟨xv, yv⟩, rfl⟩
  have hmem : vertexStab L xv yv ∈ (stabilizerGroup L).toSubgroup := by
    rw [stabilizerGroup_toSubgroup_eq]
    apply Subgroup.subset_closure
    left; exact ⟨(xv, yv), rfl⟩
  have hcomm_g : vertexStab L xv yv * g = g * vertexStab L xv yv := by
    rw [mem_centralizer_iff] at hg
    exact hg (vertexStab L xv yv) hmem
  rw [NQubitPauliGroupElement.commutes_iff_even_anticommutes] at hcomm_g ⊢
  classical
  have hfilter_eq :
      Finset.univ.filter (NQubitPauliGroupElement.anticommutesAt
        (vertexStab L xv yv).operators
        (Stabilizer.Lattice.toricXOperatorOfChain L (xChainOf L g)).operators) =
      Finset.univ.filter (NQubitPauliGroupElement.anticommutesAt
        (vertexStab L xv yv).operators g.operators) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (anticommutesAt_vertexStab_g_iff_xChain L g xv yv i).symm
  rw [hfilter_eq]
  exact hcomm_g

/-- If `g` is in the centralizer, its Z-chain is a dual cycle. -/
private lemma zChain_mem_toricDualCycles_of_centralizer (L : ℕ) [Fact (2 ≤ L)]
    (g : NQubitPauliGroupElement (numQubits L))
    (hg : g ∈ centralizer (stabilizerGroup L)) :
    zChainOf L g ∈ Stabilizer.Lattice.toricDualCycles (L := L) := by
  apply (Stabilizer.Lattice.zCommutesWithXChecks_iff_mem_toricDualCycles L (zChainOf L g)).mp
  intro x hx
  rcases hx with ⟨⟨xf, yf⟩, rfl⟩
  have hmem : faceStab L xf yf ∈ (stabilizerGroup L).toSubgroup := by
    rw [stabilizerGroup_toSubgroup_eq]
    apply Subgroup.subset_closure
    right; exact ⟨(xf, yf), rfl⟩
  have hcomm_g : faceStab L xf yf * g = g * faceStab L xf yf := by
    rw [mem_centralizer_iff] at hg
    exact hg (faceStab L xf yf) hmem
  rw [NQubitPauliGroupElement.commutes_iff_even_anticommutes] at hcomm_g ⊢
  classical
  have hfilter_eq :
      Finset.univ.filter (NQubitPauliGroupElement.anticommutesAt
        (faceStab L xf yf).operators
        (Stabilizer.Lattice.toricZOperatorOfChain L (zChainOf L g)).operators) =
      Finset.univ.filter (NQubitPauliGroupElement.anticommutesAt
        (faceStab L xf yf).operators g.operators) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (anticommutesAt_faceStab_g_iff_zChain L g xf yf i).symm
  rw [hfilter_eq]
  exact hcomm_g

/-- Weight of `toricXOperatorOfChain c` equals `edgeWeight c`. -/
private lemma weight_toricXOperatorOfChain_eq (L : ℕ) [Fact (0 < L)]
    (c : Stabilizer.Lattice.C1 L) :
    NQubitPauliGroupElement.weight (Stabilizer.Lattice.toricXOperatorOfChain L c) =
      Stabilizer.Lattice.edgeWeight (L := L) c := by
  classical
  unfold NQubitPauliGroupElement.weight Stabilizer.Lattice.edgeWeight
  refine Finset.card_bij
    (fun q (hq : q ∈ NQubitPauliOperator.support _) =>
      Classical.choose
        (show ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧ c e = 1 from by
          simp only [NQubitPauliOperator.mem_support, ne_eq,
            Stabilizer.Lattice.toricXOperatorOfChain] at hq
          by_cases h : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧ c e = 1
          · exact h
          · simp [h] at hq))
    ?hmem ?hinj ?hsurj
  · intro a ha
    have hex : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = a ∧ c e = 1 := by
      simp only [NQubitPauliOperator.mem_support, ne_eq,
        Stabilizer.Lattice.toricXOperatorOfChain] at ha
      by_cases h : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = a ∧ c e = 1
      · exact h
      · simp [h] at ha
    have hspec := Classical.choose_spec hex
    simp [Stabilizer.Lattice.mem_edgeSupport, hspec.2]
  · intro a₁ ha₁ a₂ ha₂ heq
    have hex1 : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = a₁ ∧ c e = 1 := by
      simp only [NQubitPauliOperator.mem_support, ne_eq,
        Stabilizer.Lattice.toricXOperatorOfChain] at ha₁
      by_cases h : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = a₁ ∧ c e = 1
      · exact h
      · simp [h] at ha₁
    have hex2 : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = a₂ ∧ c e = 1 := by
      simp only [NQubitPauliOperator.mem_support, ne_eq,
        Stabilizer.Lattice.toricXOperatorOfChain] at ha₂
      by_cases h : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = a₂ ∧ c e = 1
      · exact h
      · simp [h] at ha₂
    have hspec1 := Classical.choose_spec hex1
    have hspec2 := Classical.choose_spec hex2
    calc a₁ = Stabilizer.Lattice.edgeToQubitIdx L (Classical.choose hex1) := hspec1.1.symm
      _ = Stabilizer.Lattice.edgeToQubitIdx L (Classical.choose hex2) := congrArg _ heq
      _ = a₂ := hspec2.1
  · intro b hb
    refine ⟨Stabilizer.Lattice.edgeToQubitIdx L b, ?_, ?_⟩
    · have hb1 : c b = 1 := by
        have hbne : c b ≠ 0 := (Stabilizer.Lattice.mem_edgeSupport _ _).mp hb
        rcases Fin.exists_fin_two.mp ⟨c b, rfl⟩ with h | h
        · exfalso; exact hbne h
        · exact h
      have hex : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e =
          Stabilizer.Lattice.edgeToQubitIdx L b ∧ c e = 1 := ⟨b, rfl, hb1⟩
      simp only [NQubitPauliOperator.mem_support, ne_eq,
        Stabilizer.Lattice.toricXOperatorOfChain, hex, ↓reduceIte]
      decide
    · have hb1 : c b = 1 := by
        have hbne : c b ≠ 0 := (Stabilizer.Lattice.mem_edgeSupport _ _).mp hb
        rcases Fin.exists_fin_two.mp ⟨c b, rfl⟩ with h | h
        · exfalso; exact hbne h
        · exact h
      have hex : ∃ x, Stabilizer.Lattice.edgeToQubitIdx L x =
          Stabilizer.Lattice.edgeToQubitIdx L b ∧ c x = 1 := ⟨b, rfl, hb1⟩
      have hspec := Classical.choose_spec hex
      exact Stabilizer.Lattice.edgeToQubitIdx_injective L hspec.1

/-- Weight of `toricZOperatorOfChain c` equals `edgeWeight c`. -/
private lemma weight_toricZOperatorOfChain_eq (L : ℕ) [Fact (0 < L)]
    (c : Stabilizer.Lattice.C1 L) :
    NQubitPauliGroupElement.weight (Stabilizer.Lattice.toricZOperatorOfChain L c) =
      Stabilizer.Lattice.edgeWeight (L := L) c := by
  classical
  unfold NQubitPauliGroupElement.weight Stabilizer.Lattice.edgeWeight
  refine Finset.card_bij
    (fun q (hq : q ∈ NQubitPauliOperator.support _) =>
      Classical.choose
        (show ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧ c e = 1 from by
          simp only [NQubitPauliOperator.mem_support, ne_eq,
            Stabilizer.Lattice.toricZOperatorOfChain] at hq
          by_cases h : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧ c e = 1
          · exact h
          · simp [h] at hq))
    ?hmem ?hinj ?hsurj
  · intro a ha
    have hex : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = a ∧ c e = 1 := by
      simp only [NQubitPauliOperator.mem_support, ne_eq,
        Stabilizer.Lattice.toricZOperatorOfChain] at ha
      by_cases h : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = a ∧ c e = 1
      · exact h
      · simp [h] at ha
    have hspec := Classical.choose_spec hex
    simp [Stabilizer.Lattice.mem_edgeSupport, hspec.2]
  · intro a₁ ha₁ a₂ ha₂ heq
    have hex1 : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = a₁ ∧ c e = 1 := by
      simp only [NQubitPauliOperator.mem_support, ne_eq,
        Stabilizer.Lattice.toricZOperatorOfChain] at ha₁
      by_cases h : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = a₁ ∧ c e = 1
      · exact h
      · simp [h] at ha₁
    have hex2 : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = a₂ ∧ c e = 1 := by
      simp only [NQubitPauliOperator.mem_support, ne_eq,
        Stabilizer.Lattice.toricZOperatorOfChain] at ha₂
      by_cases h : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = a₂ ∧ c e = 1
      · exact h
      · simp [h] at ha₂
    have hspec1 := Classical.choose_spec hex1
    have hspec2 := Classical.choose_spec hex2
    calc a₁ = Stabilizer.Lattice.edgeToQubitIdx L (Classical.choose hex1) := hspec1.1.symm
      _ = Stabilizer.Lattice.edgeToQubitIdx L (Classical.choose hex2) := congrArg _ heq
      _ = a₂ := hspec2.1
  · intro b hb
    refine ⟨Stabilizer.Lattice.edgeToQubitIdx L b, ?_, ?_⟩
    · have hb1 : c b = 1 := by
        have hbne : c b ≠ 0 := (Stabilizer.Lattice.mem_edgeSupport _ _).mp hb
        rcases Fin.exists_fin_two.mp ⟨c b, rfl⟩ with h | h
        · exfalso; exact hbne h
        · exact h
      have hex : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e =
          Stabilizer.Lattice.edgeToQubitIdx L b ∧ c e = 1 := ⟨b, rfl, hb1⟩
      simp only [NQubitPauliOperator.mem_support, ne_eq,
        Stabilizer.Lattice.toricZOperatorOfChain, hex, ↓reduceIte]
      decide
    · have hb1 : c b = 1 := by
        have hbne : c b ≠ 0 := (Stabilizer.Lattice.mem_edgeSupport _ _).mp hb
        rcases Fin.exists_fin_two.mp ⟨c b, rfl⟩ with h | h
        · exfalso; exact hbne h
        · exact h
      have hex : ∃ x, Stabilizer.Lattice.edgeToQubitIdx L x =
          Stabilizer.Lattice.edgeToQubitIdx L b ∧ c x = 1 := ⟨b, rfl, hb1⟩
      have hspec := Classical.choose_spec hex
      exact Stabilizer.Lattice.edgeToQubitIdx_injective L hspec.1

/-- For a nontrivial logical `g`, the X-chain and Z-chain cannot both be boundaries. -/
private lemma not_both_boundary_of_nontrivial (L : ℕ) [Fact (2 ≤ L)]
    (g : NQubitPauliGroupElement (numQubits L))
    (hg : IsNontrivialLogicalOperator g (stabilizerGroup L)) :
    ¬(xChainOf L g ∈ Stabilizer.Lattice.toricBoundaries (L := L) ∧
      zChainOf L g ∈ Stabilizer.Lattice.toricDualBoundaries (L := L)) := by
  have hL0 : 0 < L := Nat.lt_of_lt_of_le (by decide : 0 < 2) (Fact.out : 2 ≤ L)
  haveI : Fact (0 < L) := ⟨hL0⟩
  rintro ⟨hxBnd, hzBnd⟩
  -- Define X-only and Z-only encodings of g
  set g_X := Stabilizer.Lattice.toricXOperatorOfChain L (xChainOf L g) with hg_X
  set g_Z := Stabilizer.Lattice.toricZOperatorOfChain L (zChainOf L g) with hg_Z
  -- Each is in the appropriate generator closure (hence in the stabilizer subgroup)
  have hgX_mem : g_X ∈ (stabilizerGroup L).toSubgroup := by
    rw [stabilizerGroup_toSubgroup_eq, subgroup]
    have : g_X ∈ Subgroup.closure (XGenerators L) :=
      (Stabilizer.Lattice.xIsPlaquetteProduct_iff_mem_toricBoundaries L (xChainOf L g)).mpr hxBnd
    apply Subgroup.closure_mono _ this
    intro x hx; right; exact hx
  have hgZ_mem : g_Z ∈ (stabilizerGroup L).toSubgroup := by
    rw [stabilizerGroup_toSubgroup_eq, subgroup]
    have : g_Z ∈ Subgroup.closure (ZGenerators L) :=
      (Stabilizer.Lattice.zIsStarProduct_iff_mem_toricDualBoundaries L (zChainOf L g)).mpr hzBnd
    apply Subgroup.closure_mono _ this
    intro x hx; left; exact hx
  -- Their product is also in the stabilizer
  have hprod_mem : g_X * g_Z ∈ (stabilizerGroup L).toSubgroup :=
    (stabilizerGroup L).toSubgroup.mul_mem hgX_mem hgZ_mem
  -- (g_X * g_Z).operators = g.operators (computed per-qubit)
  have hops_eq : (g_X * g_Z).operators = g.operators := by
    ext i
    have hX_i := toricXOf_xChain_operators_eq L g i
    have hZ_i := toricZOf_zChain_operators_eq L g i
    show ((g_X.operators i).mulOp (g_Z.operators i)).operator = g.operators i
    rw [hX_i, hZ_i]
    cases hgi : g.operators i <;>
      simp [PauliOperator.mulOp]
  -- Apply the third condition of IsNontrivialLogicalOperator
  rw [IsNontrivialLogicalOperator_iff] at hg
  obtain ⟨_, _, h_no_phase_dup⟩ := hg
  exact h_no_phase_dup (g_X * g_Z) hprod_mem hops_eq

/-- CSS bridge: full distance = min(dX, dZ). -/
theorem toricCodeN_distance_eq_min_dX_dZ (L dX dZ : ℕ) [Fact (2 ≤ L)]
    (hx : HasToricXDistance L dX) (hz : HasToricZDistance L dZ) :
    HasCodeDistance (toricStabilizerCode L) (Nat.min dX dZ) := by
  have hL0 : 0 < L := Nat.lt_of_lt_of_le (by decide : 0 < 2) (Fact.out : 2 ≤ L)
  haveI : Fact (0 < L) := ⟨hL0⟩
  obtain ⟨hdXpos, hxLB, hxWit⟩ := hx
  obtain ⟨hdZpos, hzLB, hzWit⟩ := hz
  -- Translate `IsNontrivialLogicalOperator g (toricStabilizerCode L).toStabilizerGroup`
  -- to `IsNontrivialLogicalOperator g (stabilizerGroup L)` via the subgroup equality.
  have h_subgroup_eq := toricStabilizerCode_subgroup_eq L
  have h_iff : ∀ g, IsNontrivialLogicalOperator g (toricStabilizerCode L).toStabilizerGroup ↔
      IsNontrivialLogicalOperator g (stabilizerGroup L) :=
    fun g => IsNontrivialLogicalOperator_of_toSubgroup_eq g h_subgroup_eq
  refine ⟨le_min hdXpos hdZpos, ?_, ?_⟩
  · intro g hgLogical' hgwpos
    have hgLogical := (h_iff g).mp hgLogical'
    have h_not_both := not_both_boundary_of_nontrivial L g hgLogical
    have hg_cent : g ∈ centralizer (stabilizerGroup L) :=
      (IsNontrivialLogicalOperator_iff g (stabilizerGroup L)).mp hgLogical |>.1
    have hxCyc : xChainOf L g ∈ Stabilizer.Lattice.toricCycles (L := L) :=
      xChain_mem_toricCycles_of_centralizer L g hg_cent
    have hzCyc : zChainOf L g ∈ Stabilizer.Lattice.toricDualCycles (L := L) :=
      zChain_mem_toricDualCycles_of_centralizer L g hg_cent
    by_cases hxBnd : xChainOf L g ∈ Stabilizer.Lattice.toricBoundaries (L := L)
    · by_cases hzBnd : zChainOf L g ∈ Stabilizer.Lattice.toricDualBoundaries (L := L)
      · exact absurd ⟨hxBnd, hzBnd⟩ h_not_both
      · -- Use Z-distance bound
        have hzNontrivial :
            IsNontrivialLogicalOperator
              (Stabilizer.Lattice.toricZOperatorOfChain L (zChainOf L g))
              (stabilizerGroup L) :=
          (Stabilizer.Lattice.zNontrivialLogical_iff_dualCycle_not_dualBoundary L
            (zChainOf L g)).mpr ⟨hzCyc, hzBnd⟩
        have hzType :
            NQubitPauliGroupElement.IsZTypeElement
              (Stabilizer.Lattice.toricZOperatorOfChain L (zChainOf L g)) := by
          refine ⟨rfl, ?_⟩
          intro q
          simp only [Stabilizer.Lattice.toricZOperatorOfChain]
          by_cases h : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧ zChainOf L g e = 1
          · simp [h]; exact PauliOperator.IsZType_Z
          · simp [h]; exact PauliOperator.IsZType_I
        have h_zChain_pos : 0 < Stabilizer.Lattice.edgeWeight (L := L) (zChainOf L g) := by
          rcases Nat.eq_zero_or_pos
            (Stabilizer.Lattice.edgeWeight (L := L) (zChainOf L g)) with h0 | hpos
          · exfalso
            have hzero : Stabilizer.Lattice.edgeSupport (L := L) (zChainOf L g) = ∅ := by
              rw [show Stabilizer.Lattice.edgeWeight (L := L) (zChainOf L g) =
                  (Stabilizer.Lattice.edgeSupport (L := L) (zChainOf L g)).card from rfl,
                Finset.card_eq_zero] at h0
              exact h0
            have hzChain_zero : zChainOf L g = 0 := by
              funext e
              show zChainOf L g e = 0
              by_contra hne
              have hmem : e ∈ Stabilizer.Lattice.edgeSupport (L := L) (zChainOf L g) := by
                simp [Stabilizer.Lattice.mem_edgeSupport, hne]
              rw [hzero] at hmem
              exact (Finset.notMem_empty _ hmem)
            have : zChainOf L g ∈ Stabilizer.Lattice.toricDualBoundaries (L := L) := by
              rw [hzChain_zero]; exact Submodule.zero_mem _
            exact hzBnd this
          · exact hpos
        have hwz : weight g ≥ dZ := by
          calc weight g
              ≥ Stabilizer.Lattice.edgeWeight (L := L) (zChainOf L g) :=
                weight_ge_edgeWeight_zChain L g
            _ = NQubitPauliGroupElement.weight
                  (Stabilizer.Lattice.toricZOperatorOfChain L (zChainOf L g)) :=
                (weight_toricZOperatorOfChain_eq L _).symm
            _ ≥ dZ := hzLB _ hzType hzNontrivial
                (by rw [weight_toricZOperatorOfChain_eq]; exact h_zChain_pos)
        exact le_trans (Nat.min_le_right _ _) hwz
    · have hxNontrivial :
          IsNontrivialLogicalOperator
            (Stabilizer.Lattice.toricXOperatorOfChain L (xChainOf L g))
            (stabilizerGroup L) :=
        (Stabilizer.Lattice.xNontrivialLogical_iff_cycle_not_boundary L
          (xChainOf L g)).mpr ⟨hxCyc, hxBnd⟩
      have hxType :
          NQubitPauliGroupElement.IsXTypeElement
            (Stabilizer.Lattice.toricXOperatorOfChain L (xChainOf L g)) := by
        refine ⟨rfl, ?_⟩
        intro q
        simp only [Stabilizer.Lattice.toricXOperatorOfChain]
        by_cases h : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧ xChainOf L g e = 1
        · simp [h]; exact PauliOperator.IsXType_X
        · simp [h]; exact PauliOperator.IsXType_I
      have h_xChain_pos : 0 < Stabilizer.Lattice.edgeWeight (L := L) (xChainOf L g) := by
        rcases Nat.eq_zero_or_pos
          (Stabilizer.Lattice.edgeWeight (L := L) (xChainOf L g)) with h0 | hpos
        · exfalso
          have hzero : Stabilizer.Lattice.edgeSupport (L := L) (xChainOf L g) = ∅ := by
            rw [show Stabilizer.Lattice.edgeWeight (L := L) (xChainOf L g) =
                (Stabilizer.Lattice.edgeSupport (L := L) (xChainOf L g)).card from rfl,
              Finset.card_eq_zero] at h0
            exact h0
          have hxChain_zero : xChainOf L g = 0 := by
            funext e
            show xChainOf L g e = 0
            by_contra hne
            have hmem : e ∈ Stabilizer.Lattice.edgeSupport (L := L) (xChainOf L g) := by
              simp [Stabilizer.Lattice.mem_edgeSupport, hne]
            rw [hzero] at hmem
            exact (Finset.notMem_empty _ hmem)
          have : xChainOf L g ∈ Stabilizer.Lattice.toricBoundaries (L := L) := by
            rw [hxChain_zero]; exact Submodule.zero_mem _
          exact hxBnd this
        · exact hpos
      have hwx : weight g ≥ dX := by
        calc weight g
            ≥ Stabilizer.Lattice.edgeWeight (L := L) (xChainOf L g) :=
              weight_ge_edgeWeight_xChain L g
          _ = NQubitPauliGroupElement.weight
                (Stabilizer.Lattice.toricXOperatorOfChain L (xChainOf L g)) :=
              (weight_toricXOperatorOfChain_eq L _).symm
          _ ≥ dX := hxLB _ hxType hxNontrivial
              (by rw [weight_toricXOperatorOfChain_eq]; exact h_xChain_pos)
      exact le_trans (Nat.min_le_left _ _) hwx
  · -- Witness
    by_cases hle : dX ≤ dZ
    · obtain ⟨g, _, hg_logical, hg_weight⟩ := hxWit
      refine ⟨g, (h_iff g).mpr hg_logical, ?_⟩
      rw [hg_weight]; exact (Nat.min_eq_left hle).symm
    · push_neg at hle
      obtain ⟨g, _, hg_logical, hg_weight⟩ := hzWit
      refine ⟨g, (h_iff g).mpr hg_logical, ?_⟩
      rw [hg_weight]; exact (Nat.min_eq_right (le_of_lt hle)).symm

-- ---------------------------------------------------------------------------
-- 3.  Full distance = L
-- ---------------------------------------------------------------------------

/-- Section 8.3 endpoint: the full toric-code distance is `L`. -/
theorem toricCodeN_distance_eq_L (L : ℕ) [Fact (2 ≤ L)] :
    HasCodeDistance (toricStabilizerCode L) L := by
  have hx : HasToricXDistance L L := toricCodeN_dX_eq_L L
  have hz : HasToricZDistance L L := toricCodeN_dZ_eq_L L
  simpa using toricCodeN_distance_eq_min_dX_dZ L L L hx hz

/-- Parameter-packaging: toric family has parameters `[[2L², 2, L]]`. -/
theorem toricCodeN_parameters_statement (L : ℕ) [Fact (2 ≤ L)] :
    numQubits L = 2 * L * L ∧ HasCodeDistance (toricStabilizerCode L) L :=
  ⟨rfl, toricCodeN_distance_eq_L L⟩

end ToricCodeN
end StabilizerGroup
end Quantum
