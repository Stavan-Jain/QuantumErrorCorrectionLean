import Mathlib.Tactic
import QEC.Stabilizer.Codes.ToricCodeN
import QEC.Stabilizer.Lattice.ToricLogicalCorrespondenceZ
import QEC.Stabilizer.Lattice.ToricDualWrappingInvariants
import QEC.Stabilizer.PauliGroup.NQubitElement

namespace Quantum
namespace StabilizerGroup
namespace ToricCodeN

open scoped BigOperators
open NQubitPauliGroupElement

/-!
# Z-distance = L for the toric code

Mirror of `ToricCodeNDistanceX`, using the dual chain complex:
  - `HasToricZDistance` predicate (analogue of `HasToricXDistance`)
  - Witness: vertical row of V-edges at y = 0  (weight L)
  - Lower bound: dual wrapping invariant argument
-/

-- ---------------------------------------------------------------------------
-- 1.  Z-distance predicate
-- ---------------------------------------------------------------------------

/-- Z-distance predicate: minimum weight of nontrivial Z-type logical operators. -/
def HasToricZDistance (L d : ℕ) [Fact (2 ≤ L)] : Prop :=
  d ≥ 1 ∧
  (∀ g : NQubitPauliGroupElement (numQubits L),
      NQubitPauliGroupElement.IsZTypeElement g →
      IsNontrivialLogicalOperator g (stabilizerGroup L) →
      0 < weight g →
      weight g ≥ d) ∧
  (∃ g : NQubitPauliGroupElement (numQubits L),
      NQubitPauliGroupElement.IsZTypeElement g ∧
      IsNontrivialLogicalOperator g (stabilizerGroup L) ∧
      weight g = d)

-- ---------------------------------------------------------------------------
-- 2.  Witness chain: a vertical row of V-edges
-- ---------------------------------------------------------------------------

/-- The canonical dual noncontractible cycle: V-edges at row `y = 0`. -/
def verticalVRowChain (L : ℕ) [Fact (0 < L)] : Stabilizer.Lattice.C1 L :=
  fun e =>
    match e with
    | Stabilizer.Lattice.EdgeIdx.h _ _ => 0
    | Stabilizer.Lattice.EdgeIdx.v _ y =>
        if y = Stabilizer.Lattice.zeroCoord L then (1 : ZMod 2) else 0

/-- Z-type Pauli operator encoded by the canonical vertical V-row. -/
def verticalVRowZOperator (L : ℕ) [Fact (0 < L)] :
    NQubitPauliGroupElement (Stabilizer.Lattice.toricNumQubits L) :=
  Stabilizer.Lattice.toricZOperatorOfChain L (verticalVRowChain L)

-- ---------------------------------------------------------------------------
-- 3.  The witness is a nontrivial dual cycle
-- ---------------------------------------------------------------------------

/-- The vertical V-row chain is a dual cycle (commutes with all face stabs). -/
theorem verticalVRowChain_mem_toricDualCycles (L : ℕ) [Fact (2 ≤ L)] :
    verticalVRowChain L ∈ Stabilizer.Lattice.toricDualCycles (L := L) := by
  have hL0 : 0 < L := Nat.lt_of_lt_of_le (by decide : 0 < 2) (Fact.out : 2 ≤ L)
  haveI : Fact (0 < L) := ⟨hL0⟩
  unfold Stabilizer.Lattice.toricDualCycles
  rw [LinearMap.mem_ker]
  ext ⟨x, y⟩
  simp only [Stabilizer.Lattice.toricDualBoundary, LinearMap.coe_mk, AddHom.coe_mk,
    verticalVRowChain]
  by_cases hy : y = Stabilizer.Lattice.zeroCoord L
  · subst hy
    show (0 : ZMod 2) + 0 + 1 + 1 = 0
    decide
  · simp [hy]

/-- The vertical V-row chain is not a dual boundary. -/
theorem verticalVRowChain_not_mem_toricDualBoundaries (L : ℕ) [Fact (2 ≤ L)] :
    verticalVRowChain L ∉ Stabilizer.Lattice.toricDualBoundaries (L := L) := by
  have hL0 : 0 < L := Nat.lt_of_lt_of_le (by decide : 0 < 2) (Fact.out : 2 ≤ L)
  haveI : Fact (0 < L) := ⟨hL0⟩
  intro h
  have h_vColAt : Stabilizer.Lattice.vColAt (L := L) (Stabilizer.Lattice.zeroCoord L)
      (verticalVRowChain L) = 0 :=
    Stabilizer.Lattice.vColAt_dualBoundary_zero L
      (⟨verticalVRowChain L, h⟩ : Stabilizer.Lattice.toricDualBoundaries (L := L))
  have h_compute : Stabilizer.Lattice.vColAt (L := L) (Stabilizer.Lattice.zeroCoord L)
      (verticalVRowChain L) = 1 := by
    unfold Stabilizer.Lattice.vColAt verticalVRowChain
    rw [Finset.sum_eq_single (Stabilizer.Lattice.zeroCoord L)]
    · simp
    · intro b _ hbne
      simp [hbne]
    · intro hcontra; exact absurd (Finset.mem_univ _) hcontra
  rw [h_compute] at h_vColAt
  exact absurd h_vColAt (by decide)

/-- The vertical V-row chain has edge-weight `L`. -/
theorem verticalVRowChain_edgeWeight_eq_L (L : ℕ) [Fact (2 ≤ L)] :
    Stabilizer.Lattice.edgeWeight (L := L) (verticalVRowChain L) = L := by
  have hL0 : 0 < L := Nat.lt_of_lt_of_le (by decide : 0 < 2) (Fact.out : 2 ≤ L)
  haveI : Fact (0 < L) := ⟨hL0⟩
  let z0 : Fin L := Stabilizer.Lattice.zeroCoord L
  let vertAtZero : Finset (Stabilizer.Lattice.EdgeIdx L) :=
    (Finset.univ.image (fun x : Fin L => Stabilizer.Lattice.EdgeIdx.v x z0))
  have hsupport :
      Stabilizer.Lattice.edgeSupport (L := L) (verticalVRowChain L) = vertAtZero := by
    ext e
    constructor
    · intro he
      have hne : verticalVRowChain L e ≠ 0 := by
        simpa [Stabilizer.Lattice.mem_edgeSupport] using he
      cases e with
      | h x y =>
          simp [verticalVRowChain] at hne
      | v x y =>
          by_cases hy : y = z0
          · subst hy
            refine Finset.mem_image.mpr ?_
            exact ⟨x, Finset.mem_univ x, rfl⟩
          · have hy' : y = z0 := by
              simpa [verticalVRowChain] using hne
            exact (hy hy').elim
    · intro he
      rcases Finset.mem_image.mp he with ⟨x, -, hx⟩
      subst hx
      simp [Stabilizer.Lattice.mem_edgeSupport, verticalVRowChain, z0]
  have hinj : Function.Injective (fun x : Fin L => Stabilizer.Lattice.EdgeIdx.v x z0) := by
    intro a b h
    cases h
    rfl
  have hcard : vertAtZero.card = L := by
    calc
      vertAtZero.card
          = (Finset.univ.image (fun x : Fin L => Stabilizer.Lattice.EdgeIdx.v x z0)).card := rfl
      _ = (Finset.univ : Finset (Fin L)).card := by
        exact Finset.card_image_of_injective
          (s := (Finset.univ : Finset (Fin L)))
          (f := fun x : Fin L => Stabilizer.Lattice.EdgeIdx.v x z0)
          (by
            intro a b hab
            exact hinj hab)
      _ = L := by simp
  calc
    Stabilizer.Lattice.edgeWeight (L := L) (verticalVRowChain L)
        = (Stabilizer.Lattice.edgeSupport (L := L) (verticalVRowChain L)).card := rfl
    _ = vertAtZero.card := by rw [hsupport]
    _ = L := hcard

-- ---------------------------------------------------------------------------
-- 4.  Existence of a nontrivial Z-logical of weight L
-- ---------------------------------------------------------------------------

/-- Upper-bound witness: a nontrivial Z-type logical of weight exactly `L`. -/
theorem exists_nontrivial_z_logical_weight_eq_L (L : ℕ) [Fact (2 ≤ L)] :
    ∃ g : NQubitPauliGroupElement (numQubits L),
      NQubitPauliGroupElement.IsZTypeElement g ∧
      IsNontrivialLogicalOperator g (stabilizerGroup L) ∧
      weight g = L := by
  have hL0 : 0 < L := Nat.lt_of_lt_of_le (by decide : 0 < 2) (Fact.out : 2 ≤ L)
  haveI : Fact (0 < L) := ⟨hL0⟩
  refine ⟨verticalVRowZOperator L, ?_, ?_, ?_⟩
  · unfold verticalVRowZOperator NQubitPauliGroupElement.IsZTypeElement
    simp +decide [Stabilizer.Lattice.toricZOperatorOfChain]
    intro q
    by_cases h : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧ verticalVRowChain L e = 1
    · simp +decide [h]
      exact PauliOperator.IsZType_Z
    · simp +decide [h]
      exact PauliOperator.IsZType_I
  · apply
      (Quantum.Stabilizer.Lattice.zNontrivialLogical_iff_dualCycle_not_dualBoundary L
        (verticalVRowChain L)).2
    exact ⟨verticalVRowChain_mem_toricDualCycles L, verticalVRowChain_not_mem_toricDualBoundaries L⟩
  · convert verticalVRowChain_edgeWeight_eq_L L
    unfold verticalVRowZOperator Stabilizer.Lattice.toricZOperatorOfChain
    unfold NQubitPauliGroupElement.weight Stabilizer.Lattice.edgeWeight
    simp +decide
    refine Finset.card_bij
      (fun q hq =>
        Classical.choose
          (show ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧ verticalVRowChain L e = 1 from by
            simpa [Finset.mem_filter] using hq))
      ?hmem ?hinj ?hsurj
    · intro a ha
      have hspec := Classical.choose_spec
        (show ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = a ∧ verticalVRowChain L e = 1 from by
          simpa [Finset.mem_filter] using ha)
      simp [Stabilizer.Lattice.edgeSupport, hspec.2]
    · intro a₁ ha₁ a₂ ha₂ h
      have hspec1 := Classical.choose_spec
        (show ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = a₁ ∧ verticalVRowChain L e = 1 from by
          simpa [Finset.mem_filter] using ha₁)
      have hspec2 := Classical.choose_spec
        (show ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = a₂ ∧ verticalVRowChain L e = 1 from by
          simpa [Finset.mem_filter] using ha₂)
      calc
        a₁ = Stabilizer.Lattice.edgeToQubitIdx L
              (Classical.choose
                (show ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = a₁ ∧
                    verticalVRowChain L e = 1 from by
                  simpa [Finset.mem_filter] using ha₁)) := by simpa using hspec1.1.symm
        _ = Stabilizer.Lattice.edgeToQubitIdx L
              (Classical.choose
                (show ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = a₂ ∧
                    verticalVRowChain L e = 1 from by
                  simpa [Finset.mem_filter] using ha₂)) := by
                exact congrArg (Stabilizer.Lattice.edgeToQubitIdx L) h
        _ = a₂ := by simpa using hspec2.1
    · intro b hb
      refine ⟨Stabilizer.Lattice.edgeToQubitIdx L b, ?_, ?_⟩
      · have hb1 : verticalVRowChain L b = 1 := by
          have hbne : verticalVRowChain L b ≠ 0 := by
            simpa [Stabilizer.Lattice.mem_edgeSupport] using hb
          exact Or.resolve_left (Fin.exists_fin_two.mp (by aesop)) hbne
        simp
        exact ⟨b, rfl, hb1⟩
      · have hb1 : verticalVRowChain L b = 1 := by
          have hbne : verticalVRowChain L b ≠ 0 := by
            simpa [Stabilizer.Lattice.mem_edgeSupport] using hb
          exact Or.resolve_left (Fin.exists_fin_two.mp (by aesop)) hbne
        have hspec := Classical.choose_spec
          (show ∃ x,
              Stabilizer.Lattice.edgeToQubitIdx L x = Stabilizer.Lattice.edgeToQubitIdx L b ∧
              verticalVRowChain L x = 1 from ⟨b, rfl, hb1⟩)
        exact Stabilizer.Lattice.edgeToQubitIdx_injective L hspec.1

-- ---------------------------------------------------------------------------
-- 5.  Lower bound: every nontrivial Z-logical has weight ≥ L
-- ---------------------------------------------------------------------------

set_option maxHeartbeats 1000000 in
-- The lower-bound proof expands many finite sums and support decompositions on the dual lattice.
/-- Lower bound: every nontrivial Z-type logical operator has weight ≥ L. -/
theorem nontrivial_z_logical_weight_ge_L (L : ℕ) [Fact (2 ≤ L)]
    (g : NQubitPauliGroupElement (numQubits L))
    (hgZ : NQubitPauliGroupElement.IsZTypeElement g)
    (hgLogical : IsNontrivialLogicalOperator g (stabilizerGroup L)) :
    weight g ≥ L := by
  have hL0 : 0 < L := Nat.lt_of_lt_of_le (by decide : 0 < 2) (Fact.out : 2 ≤ L)
  haveI : Fact (0 < L) := ⟨hL0⟩
  obtain ⟨c, hc⟩ :
      ∃ c : Stabilizer.Lattice.C1 L, g = Stabilizer.Lattice.toricZOperatorOfChain L c := by
    have := show
      ∀ g : NQubitPauliGroupElement (numQubits L),
        g.IsZTypeElement →
          ∃ c : Stabilizer.Lattice.C1 L, g = Stabilizer.Lattice.toricZOperatorOfChain L c from by
      intro g hgZ
      unfold Stabilizer.Lattice.toricZOperatorOfChain
      use fun e =>
        if g.operators (Stabilizer.Lattice.edgeToQubitIdx L e) = PauliOperator.Z then 1 else 0
      cases g
      simp_all +decide [NQubitPauliGroupElement.IsZTypeElement]
      ext q
      split_ifs <;> simp_all +decide [NQubitPauliOperator.IsZType]
      · grind
      · have h_edge_univ : ∃ e : Stabilizer.Lattice.EdgeIdx L,
            Stabilizer.Lattice.edgeToQubitIdx L e = q := by
          have h_image :
              Finset.image (Stabilizer.Lattice.edgeToQubitIdx L)
                  (Finset.univ : Finset (Stabilizer.Lattice.EdgeIdx L)) = Finset.univ := by
            refine Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_
            rw [Finset.card_image_of_injective _ (Stabilizer.Lattice.edgeToQubitIdx_injective L)]
            simp +decide [Finset.card_univ]
          exact
            Finset.mem_image.mp (h_image.symm ▸ Finset.mem_univ q) |>
              Exists.imp (fun x hx => hx.2)
        cases h : ‹NQubitPauliOperator (numQubits L)› q <;>
          simp_all +decide [PauliOperator.IsZType]
        all_goals (try cases hgZ.2 q <;> aesop)
    exact this g hgZ
  have h_dualCycle :
      c ∈ Stabilizer.Lattice.toricDualCycles (L := L) ∧
        c ∉ Stabilizer.Lattice.toricDualBoundaries (L := L) := by
    rw [hc] at hgLogical
    exact (Stabilizer.Lattice.zNontrivialLogical_iff_dualCycle_not_dualBoundary L c).mp hgLogical
  have h_weight : Stabilizer.Lattice.edgeWeight (L := L) c ≥ L := by
    have h_invariant_nonzero :
        Stabilizer.Lattice.hRowAt (L := L) (Stabilizer.Lattice.zeroCoord L) c ≠ 0 ∨
          Stabilizer.Lattice.vColAt (L := L) (Stabilizer.Lattice.zeroCoord L) c ≠ 0 := by
      have h_phi :
          Stabilizer.Lattice.phiDual (L := L) (Submodule.Quotient.mk ⟨c, h_dualCycle.left⟩) ≠
            (0, 0) := by
        intro h
        have := Stabilizer.Lattice.phiDual_injective (L := L)
        simp_all +decide
        have := @this
          (Submodule.Quotient.mk ⟨c, h_dualCycle.1⟩)
          (Submodule.Quotient.mk ⟨0, by exact Submodule.zero_mem _⟩)
        simp_all +decide
        simp_all +decide [Stabilizer.Lattice.phiDual_liftQ_eq]
        simp_all +decide [Stabilizer.Lattice.hRowAt, Stabilizer.Lattice.vColAt]
        rw [Submodule.Quotient.eq] at this
        aesop
      contrapose! h_phi
      rw [Stabilizer.Lattice.phiDual_liftQ_eq]
      aesop
    rcases h_invariant_nonzero with hH | hV
    · -- hRowAt at zeroCoord nonzero. Each row has ≥ 1 nonzero h-edge.
      have h_perCol :
          ∀ y : Fin L,
            (Finset.univ.filter
              (fun x : Fin L => c (Stabilizer.Lattice.EdgeIdx.h x y) ≠ 0)).card ≥ 1 := by
        intro y
        have h_sum :
            ∑ x : Fin L, c (Stabilizer.Lattice.EdgeIdx.h x y) =
              ∑ x : Fin L, c (Stabilizer.Lattice.EdgeIdx.h x (Stabilizer.Lattice.zeroCoord L)) := by
          have := Stabilizer.Lattice.hRowAt_independent_on_dualCycles (L := L)
            ⟨c, h_dualCycle.1⟩ y (Stabilizer.Lattice.zeroCoord L)
          simpa [Stabilizer.Lattice.hRowAt] using this
        contrapose! h_sum
        simp_all +decide
        exact Ne.symm ‹_›
      have h_weight :
          (Finset.univ.filter (fun e : Stabilizer.Lattice.EdgeIdx L => c e ≠ 0)).card ≥
            (Finset.univ : Finset (Fin L)).sum
              (fun y =>
                (Finset.univ.filter
                  (fun x : Fin L => c (Stabilizer.Lattice.EdgeIdx.h x y) ≠ 0)).card) := by
        have h_subset :
            (Finset.univ.biUnion
              (fun y : Fin L =>
                Finset.image (fun x : Fin L => Stabilizer.Lattice.EdgeIdx.h x y)
                  (Finset.univ.filter
                    (fun x : Fin L => c (Stabilizer.Lattice.EdgeIdx.h x y) ≠ 0)))).card ≤
            (Finset.univ.filter (fun e : Stabilizer.Lattice.EdgeIdx L => c e ≠ 0)).card := by
          refine Finset.card_le_card ?_
          grind +splitImp
        rw [Finset.card_biUnion] at h_subset
        · exact h_subset.trans'
            (Finset.sum_le_sum
              (fun _ _ => by
                rw [Finset.card_image_of_injective _ (fun x y hxy => by injection hxy)]))
        · intros y hy z hz hyz
          simp_all +decide [Finset.disjoint_left]
          grind
      exact le_trans
        (by
          simpa using
            Finset.sum_le_sum
              (fun y (_ : y ∈ Finset.univ) => h_perCol y))
        h_weight
    · -- vColAt at zeroCoord nonzero. Each column has ≥ 1 nonzero v-edge.
      have h_perRow :
          ∀ x : Fin L,
            (Finset.univ.filter
              (fun y : Fin L => c (Stabilizer.Lattice.EdgeIdx.v x y) ≠ 0)).card ≥ 1 := by
        intro x
        have h_sum :
            ∑ y : Fin L, c (Stabilizer.Lattice.EdgeIdx.v x y) =
              ∑ y : Fin L, c (Stabilizer.Lattice.EdgeIdx.v (Stabilizer.Lattice.zeroCoord L) y) := by
          have := Stabilizer.Lattice.vColAt_independent_on_dualCycles (L := L)
            ⟨c, h_dualCycle.1⟩ x (Stabilizer.Lattice.zeroCoord L)
          simpa [Stabilizer.Lattice.vColAt] using this
        contrapose! h_sum
        simp_all +decide
        exact Ne.symm ‹_›
      have h_weight :
          (Finset.univ.filter (fun e : Stabilizer.Lattice.EdgeIdx L => c e ≠ 0)).card ≥
            (Finset.univ : Finset (Fin L)).sum
              (fun x =>
                (Finset.univ.filter
                  (fun y : Fin L => c (Stabilizer.Lattice.EdgeIdx.v x y) ≠ 0)).card) := by
        have h_subset :
            (Finset.univ.biUnion
              (fun x : Fin L =>
                Finset.image (fun y : Fin L => Stabilizer.Lattice.EdgeIdx.v x y)
                  (Finset.univ.filter
                    (fun y : Fin L => c (Stabilizer.Lattice.EdgeIdx.v x y) ≠ 0)))).card ≤
            (Finset.univ.filter (fun e : Stabilizer.Lattice.EdgeIdx L => c e ≠ 0)).card := by
          refine Finset.card_le_card ?_
          grind +splitImp
        rw [Finset.card_biUnion] at h_subset
        · exact h_subset.trans'
            (Finset.sum_le_sum
              (fun _ _ => by
                rw [Finset.card_image_of_injective _ (fun x y hxy => by injection hxy)]))
        · intros x hx z hz hxz
          simp_all +decide [Finset.disjoint_left]
          grind
      exact le_trans
        (by
          simpa using
            Finset.sum_le_sum
              (fun x (_ : x ∈ Finset.univ) => h_perRow x))
        h_weight
  rw [hc]
  refine le_trans h_weight ?_
  unfold Stabilizer.Lattice.toricZOperatorOfChain
  unfold Stabilizer.Lattice.edgeWeight NQubitPauliGroupElement.weight
  refine le_of_eq ?_
  refine Finset.card_bij (fun q hq => Stabilizer.Lattice.edgeToQubitIdx L q) ?_ ?_ ?_ <;>
    simp +decide [Stabilizer.Lattice.edgeSupport]
  · intro a ha
    use a
    simp +decide
    exact Or.resolve_left (Fin.exists_fin_two.mp (by aesop)) ha
  · intro a₁ ha₁ a₂ ha₂ h
    have := Stabilizer.Lattice.edgeToQubitIdx_injective L h
    aesop
  · exact fun b x hx hx' => ⟨x, by aesop⟩

-- ---------------------------------------------------------------------------
-- 6.  Z-distance endpoint
-- ---------------------------------------------------------------------------

/-- Section 8.3: Z-distance equals `L`. -/
theorem toricCodeN_dZ_eq_L (L : ℕ) [Fact (2 ≤ L)] :
    HasToricZDistance L L := by
  refine ⟨?_, ?_, ?_⟩
  · have hL : 2 ≤ L := Fact.out; omega
  · intro g hgZ hgLogical _
    exact nontrivial_z_logical_weight_ge_L L g hgZ hgLogical
  · exact exists_nontrivial_z_logical_weight_eq_L L

-- ---------------------------------------------------------------------------
-- Horizontal Z-row: the column-0 sister of `verticalVRowChain`/`verticalVRowZOperator`
-- ---------------------------------------------------------------------------

/-- Horizontal Z-row chain: H-edges along column `x = zeroCoord`. -/
def horizontalHRowChain (L : ℕ) [Fact (0 < L)] : Stabilizer.Lattice.C1 L :=
  fun e =>
    match e with
    | Stabilizer.Lattice.EdgeIdx.h x _ =>
        if x = Stabilizer.Lattice.zeroCoord L then (1 : ZMod 2) else 0
    | Stabilizer.Lattice.EdgeIdx.v _ _ => 0

/-- Z-type Pauli operator encoded by the horizontal H-row chain. -/
def horizontalHRowZOperator (L : ℕ) [Fact (0 < L)] :
    NQubitPauliGroupElement (Stabilizer.Lattice.toricNumQubits L) :=
  Stabilizer.Lattice.toricZOperatorOfChain L (horizontalHRowChain L)

/-- The horizontal Z-row chain is a dual cycle. -/
theorem horizontalHRowChain_mem_toricDualCycles (L : ℕ) [Fact (2 ≤ L)] :
    horizontalHRowChain L ∈ Stabilizer.Lattice.toricDualCycles (L := L) := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  unfold Stabilizer.Lattice.toricDualCycles
  rw [LinearMap.mem_ker]
  ext ⟨x, y⟩
  simp only [Stabilizer.Lattice.toricDualBoundary, LinearMap.coe_mk, AddHom.coe_mk,
    horizontalHRowChain]
  by_cases hx : x = Stabilizer.Lattice.zeroCoord L
  · subst hx
    show (1 : ZMod 2) + 1 + 0 + 0 = 0
    decide
  · simp [hx]

/-- The horizontal Z-row chain is not a dual boundary (its `hRowAt` invariant is 1). -/
theorem horizontalHRowChain_not_mem_toricDualBoundaries (L : ℕ) [Fact (2 ≤ L)] :
    horizontalHRowChain L ∉ Stabilizer.Lattice.toricDualBoundaries (L := L) := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  intro h
  have h_hRowAt : Stabilizer.Lattice.hRowAt (L := L) (Stabilizer.Lattice.zeroCoord L)
      (horizontalHRowChain L) = 0 :=
    Stabilizer.Lattice.hRowAt_dualBoundary_zero (L := L)
      ⟨horizontalHRowChain L, h⟩
  have h_compute : Stabilizer.Lattice.hRowAt (L := L) (Stabilizer.Lattice.zeroCoord L)
      (horizontalHRowChain L) = 1 := by
    unfold Stabilizer.Lattice.hRowAt horizontalHRowChain
    rw [Finset.sum_eq_single (Stabilizer.Lattice.zeroCoord L)]
    · simp
    · intro b _ hbne
      simp [hbne]
    · intro hcontra; exact absurd (Finset.mem_univ _) hcontra
  rw [h_compute] at h_hRowAt
  exact absurd h_hRowAt (by decide)

/-- The horizontal Z-row chain has edge weight `L`. -/
theorem horizontalHRowChain_edgeWeight_eq_L (L : ℕ) [Fact (2 ≤ L)] :
    Stabilizer.Lattice.edgeWeight (L := L) (horizontalHRowChain L) = L := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  let z0 : Fin L := Stabilizer.Lattice.zeroCoord L
  let horizCol : Finset (Stabilizer.Lattice.EdgeIdx L) :=
    (Finset.univ.image (fun y : Fin L => Stabilizer.Lattice.EdgeIdx.h z0 y))
  have hsupport :
      Stabilizer.Lattice.edgeSupport (L := L) (horizontalHRowChain L) = horizCol := by
    ext e
    constructor
    · intro he
      have hne : horizontalHRowChain L e ≠ 0 := by
        simpa [Stabilizer.Lattice.mem_edgeSupport] using he
      cases e with
      | h x y =>
          by_cases hx : x = z0
          · subst hx
            refine Finset.mem_image.mpr ?_
            exact ⟨y, Finset.mem_univ y, rfl⟩
          · have hx' : x = z0 := by simpa [horizontalHRowChain] using hne
            exact (hx hx').elim
      | v x y => simp [horizontalHRowChain] at hne
    · intro he
      rcases Finset.mem_image.mp he with ⟨y, -, hy⟩
      subst hy
      simp [Stabilizer.Lattice.mem_edgeSupport, horizontalHRowChain, z0]
  have hinj : Function.Injective (fun y : Fin L => Stabilizer.Lattice.EdgeIdx.h z0 y) := by
    intro a b h; cases h; rfl
  have hcard : horizCol.card = L := by
    calc
      horizCol.card
          = (Finset.univ.image (fun y : Fin L => Stabilizer.Lattice.EdgeIdx.h z0 y)).card := rfl
      _ = (Finset.univ : Finset (Fin L)).card := by
          exact Finset.card_image_of_injective
            (s := (Finset.univ : Finset (Fin L)))
            (f := fun y : Fin L => Stabilizer.Lattice.EdgeIdx.h z0 y)
            (by intro a b hab; exact hinj hab)
      _ = L := by simp
  calc
    Stabilizer.Lattice.edgeWeight (L := L) (horizontalHRowChain L)
        = (Stabilizer.Lattice.edgeSupport (L := L) (horizontalHRowChain L)).card := rfl
    _ = horizCol.card := by rw [hsupport]
    _ = L := hcard

/-- The horizontal Z-row operator is Z-type. -/
theorem horizontalHRowZOperator_isZType (L : ℕ) [Fact (0 < L)] :
    NQubitPauliGroupElement.IsZTypeElement (horizontalHRowZOperator L) := by
  unfold horizontalHRowZOperator NQubitPauliGroupElement.IsZTypeElement
  refine ⟨rfl, fun q => ?_⟩
  by_cases h : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧ horizontalHRowChain L e = 1
  · right; simp [Stabilizer.Lattice.toricZOperatorOfChain, h]
  · left; simp [Stabilizer.Lattice.toricZOperatorOfChain, h]

/-- The vertical V-row Z-operator is Z-type. -/
theorem verticalVRowZOperator_isZType (L : ℕ) [Fact (0 < L)] :
    NQubitPauliGroupElement.IsZTypeElement (verticalVRowZOperator L) := by
  unfold verticalVRowZOperator NQubitPauliGroupElement.IsZTypeElement
  refine ⟨rfl, fun q => ?_⟩
  by_cases h : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧ verticalVRowChain L e = 1
  · right; simp [Stabilizer.Lattice.toricZOperatorOfChain, h]
  · left; simp [Stabilizer.Lattice.toricZOperatorOfChain, h]

end ToricCodeN
end StabilizerGroup
end Quantum
