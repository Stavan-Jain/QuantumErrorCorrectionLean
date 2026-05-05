import Mathlib.Tactic
import QEC.Stabilizer.Codes.ToricCodeN
import QEC.Stabilizer.Lattice.ToricLogicalCorrespondenceX
import QEC.Stabilizer.Lattice.ToricWrappingInvariants
import QEC.Stabilizer.PauliGroup.NQubitElement


namespace Quantum
namespace StabilizerGroup
namespace ToricCodeN

open scoped BigOperators
open NQubitPauliGroupElement

/-- Canonical horizontal noncontractible cycle used for the X-distance upper bound witness. -/
def horizontalLoopChain (L : ℕ) [Fact (0 < L)] : Stabilizer.Lattice.C1 L :=
  fun e =>
    match e with
    | Stabilizer.Lattice.EdgeIdx.h _ y =>
        if y = Stabilizer.Lattice.zeroCoord L then (1 : ZMod 2) else 0
    | Stabilizer.Lattice.EdgeIdx.v _ _ => 0

/-- X-type Pauli operator encoded by the canonical horizontal loop cycle. -/
def horizontalLoopXOperator (L : ℕ) [Fact (0 < L)] :
    NQubitPauliGroupElement (Stabilizer.Lattice.toricNumQubits L) :=
  Stabilizer.Lattice.toricXOperatorOfChain L (horizontalLoopChain L)

/-- X-distance predicate specialized to toric-code X-type logical operators. -/
def HasToricXDistance (L d : ℕ) [Fact (2 ≤ L)] : Prop :=
  d ≥ 1 ∧
  (∀ g : NQubitPauliGroupElement (numQubits L),
      NQubitPauliGroupElement.IsXTypeElement g →
      IsNontrivialLogicalOperator g (stabilizerGroup L) →
      0 < weight g →
      weight g ≥ d) ∧
  (∃ g : NQubitPauliGroupElement (numQubits L),
      NQubitPauliGroupElement.IsXTypeElement g ∧
      IsNontrivialLogicalOperator g (stabilizerGroup L) ∧
      weight g = d)

/-- Section-8 witness: the canonical horizontal loop is a toric 1-cycle. -/
theorem horizontalLoopChain_mem_toricCycles (L : ℕ) [Fact (2 ≤ L)] :
    horizontalLoopChain L ∈ Stabilizer.Lattice.toricCycles (L := L) := by
  unfold Stabilizer.Lattice.toricCycles;
  unfold Stabilizer.Lattice.toricBoundary1 horizontalLoopChain; simp +decide ;
  ext ⟨ x, y ⟩ ; aesop

/-- Section-8 witness: the canonical horizontal loop is not a toric 1-boundary. -/
theorem horizontalLoopChain_not_mem_toricBoundaries (L : ℕ) [Fact (2 ≤ L)] :
    horizontalLoopChain L ∉ Stabilizer.Lattice.toricBoundaries (L := L) := by
  have h_hAt_zero :
      Stabilizer.Lattice.hAt (L := L) (Stabilizer.Lattice.zeroCoord L)
        (horizontalLoopChain L) = 1 := by
    unfold Stabilizer.Lattice.hAt
    unfold horizontalLoopChain
    aesop
  intro h
  have :=
    h_hAt_zero ▸ Stabilizer.Lattice.h_boundary_zero (L := L) ⟨horizontalLoopChain L, h⟩
  contradiction

/-- Section-8 witness: canonical horizontal loop chain has edge-weight `L`. -/
theorem horizontalLoopChain_edgeWeight_eq_L (L : ℕ) [Fact (2 ≤ L)] :
    Stabilizer.Lattice.edgeWeight (L := L) (horizontalLoopChain L) = L := by
  let z0 : Fin L := Stabilizer.Lattice.zeroCoord L
  let horizAtZero : Finset (Stabilizer.Lattice.EdgeIdx L) :=
    (Finset.univ.image (fun x : Fin L => Stabilizer.Lattice.EdgeIdx.h x z0))
  have hsupport :
      Stabilizer.Lattice.edgeSupport (L := L) (horizontalLoopChain L) = horizAtZero := by
    ext e
    constructor
    · intro he
      have hne : horizontalLoopChain L e ≠ 0 := by
        simpa [Stabilizer.Lattice.mem_edgeSupport] using he
      cases e with
      | h x y =>
          by_cases hy : y = z0
          · subst hy
            refine Finset.mem_image.mpr ?_
            exact ⟨x, Finset.mem_univ x, rfl⟩
          · have hy' : y = z0 := by
              simpa [horizontalLoopChain] using hne
            exact (hy hy').elim
      | v x y =>
          simp [horizontalLoopChain] at hne
    · intro he
      rcases Finset.mem_image.mp he with ⟨x, -, hx⟩
      subst hx
      simp [Stabilizer.Lattice.mem_edgeSupport, horizontalLoopChain, z0]
  have hinj : Function.Injective (fun x : Fin L => Stabilizer.Lattice.EdgeIdx.h x z0) := by
    intro a b h
    cases h
    rfl
  have hcard : horizAtZero.card = L := by
    calc
      horizAtZero.card
          = (Finset.univ.image (fun x : Fin L => Stabilizer.Lattice.EdgeIdx.h x z0)).card := rfl
      _ = (Finset.univ : Finset (Fin L)).card := by
        exact Finset.card_image_of_injective
          (s := (Finset.univ : Finset (Fin L)))
          (f := fun x : Fin L => Stabilizer.Lattice.EdgeIdx.h x z0)
          (by
            intro a b hab
            exact hinj hab)
      _ = L := by simp
  calc
    Stabilizer.Lattice.edgeWeight (L := L) (horizontalLoopChain L)
        = (Stabilizer.Lattice.edgeSupport (L := L) (horizontalLoopChain L)).card := rfl
    _ = horizAtZero.card := by rw [hsupport]
    _ = L := hcard

/-- Section-8 upper-bound witness packaged as a nontrivial X logical of weight `L`. -/

theorem exists_nontrivial_x_logical_weight_eq_L (L : ℕ) [Fact (2 ≤ L)] :
    ∃ g : NQubitPauliGroupElement (numQubits L),
      NQubitPauliGroupElement.IsXTypeElement g ∧
      IsNontrivialLogicalOperator g (stabilizerGroup L) ∧
      weight g = L := by
  refine ⟨horizontalLoopXOperator L, ?_, ?_, ?_⟩
  · unfold horizontalLoopXOperator NQubitPauliGroupElement.IsXTypeElement
    simp +decide [Stabilizer.Lattice.toricXOperatorOfChain]
    intro q
    by_cases h : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧ horizontalLoopChain L e = 1
    · simp +decide [h]
      exact PauliOperator.IsXType_X
    · simp +decide [h]
      exact PauliOperator.IsXType_I
  · apply
      (Quantum.Stabilizer.Lattice.xNontrivialLogical_iff_cycle_not_boundary L
        (horizontalLoopChain L)).2
    exact ⟨horizontalLoopChain_mem_toricCycles L, horizontalLoopChain_not_mem_toricBoundaries L⟩
  · convert horizontalLoopChain_edgeWeight_eq_L L;
    unfold horizontalLoopXOperator Stabilizer.Lattice.toricXOperatorOfChain;
    unfold NQubitPauliGroupElement.weight Stabilizer.Lattice.edgeWeight
    simp +decide
    refine Finset.card_bij
      (fun q hq =>
        Classical.choose
          (show ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧ horizontalLoopChain L e = 1 from by
            simpa [Finset.mem_filter] using hq))
      ?hmem ?hinj ?hsurj
    · intro a ha
      have hspec := Classical.choose_spec
        (show ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = a ∧ horizontalLoopChain L e = 1 from by
          simpa [Finset.mem_filter] using ha)
      simp [Stabilizer.Lattice.edgeSupport, hspec.2]
    · intro a₁ ha₁ a₂ ha₂ h
      have hspec1 := Classical.choose_spec
        (show ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = a₁ ∧ horizontalLoopChain L e = 1 from by
          simpa [Finset.mem_filter] using ha₁)
      have hspec2 := Classical.choose_spec
        (show ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = a₂ ∧ horizontalLoopChain L e = 1 from by
          simpa [Finset.mem_filter] using ha₂)
      calc
        a₁ = Stabilizer.Lattice.edgeToQubitIdx L
              (Classical.choose
                (show ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = a₁ ∧
                    horizontalLoopChain L e = 1 from by
                  simpa [Finset.mem_filter] using ha₁)) := by simpa using hspec1.1.symm
        _ = Stabilizer.Lattice.edgeToQubitIdx L
              (Classical.choose
                (show ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = a₂ ∧
                    horizontalLoopChain L e = 1 from by
                  simpa [Finset.mem_filter] using ha₂)) := by
                exact congrArg (Stabilizer.Lattice.edgeToQubitIdx L) h
        _ = a₂ := by simpa using hspec2.1
    · intro b hb
      refine ⟨Stabilizer.Lattice.edgeToQubitIdx L b, ?_, ?_⟩
      · have hb1 : horizontalLoopChain L b = 1 := by
          have hbne : horizontalLoopChain L b ≠ 0 := by
            simpa [Stabilizer.Lattice.mem_edgeSupport] using hb
          exact Or.resolve_left (Fin.exists_fin_two.mp (by aesop)) hbne
        simp
        exact ⟨b, rfl, hb1⟩
      · have hb1 : horizontalLoopChain L b = 1 := by
          have hbne : horizontalLoopChain L b ≠ 0 := by
            simpa [Stabilizer.Lattice.mem_edgeSupport] using hb
          exact Or.resolve_left (Fin.exists_fin_two.mp (by aesop)) hbne
        have hspec := Classical.choose_spec
          (show ∃ x,
              Stabilizer.Lattice.edgeToQubitIdx L x = Stabilizer.Lattice.edgeToQubitIdx L b ∧
              horizontalLoopChain L x = 1 from ⟨b, rfl, hb1⟩)
        exact Stabilizer.Lattice.edgeToQubitIdx_injective L hspec.1

/-- Section 8.1 scaffold: X-distance upper bound `dX ≤ L`. -/
theorem xDistance_upper_bound (L : ℕ) [Fact (2 ≤ L)] :
    ∃ g : NQubitPauliGroupElement (numQubits L),
      NQubitPauliGroupElement.IsXTypeElement g ∧
      IsNontrivialLogicalOperator g (stabilizerGroup L) ∧
      weight g ≤ L := by
  rcases exists_nontrivial_x_logical_weight_eq_L L with ⟨g, hgX, hgLogical, hgwt⟩
  refine ⟨g, hgX, hgLogical, ?_⟩
  simp [hgwt]

set_option maxHeartbeats 1000000 in
-- The lower-bound proof expands many finite sums and support decompositions.
theorem nontrivial_x_logical_weight_ge_L (L : ℕ) [Fact (2 ≤ L)]
    (g : NQubitPauliGroupElement (numQubits L))
    (hgX : NQubitPauliGroupElement.IsXTypeElement g)
    (hgLogical : IsNontrivialLogicalOperator g (stabilizerGroup L)) :
    weight g ≥ L := by
  obtain ⟨c, hc⟩ :
      ∃ c : Stabilizer.Lattice.C1 L, g = Stabilizer.Lattice.toricXOperatorOfChain L c := by
    have := show
      ∀ g : NQubitPauliGroupElement (numQubits L),
        g.IsXTypeElement →
          ∃ c : Stabilizer.Lattice.C1 L, g = Stabilizer.Lattice.toricXOperatorOfChain L c from by
      intro g hgX
      unfold Stabilizer.Lattice.toricXOperatorOfChain
      use fun e =>
        if g.operators (Stabilizer.Lattice.edgeToQubitIdx L e) = PauliOperator.X then 1 else 0
      cases g
      simp_all +decide [NQubitPauliGroupElement.IsXTypeElement]
      ext q
      split_ifs <;> simp_all +decide [NQubitPauliOperator.IsXType]
      · grind
      · cases h : ‹NQubitPauliOperator (numQubits L)› q <;> simp_all +decide [PauliOperator.IsXType]
        · have h_edge : ∃ e : Stabilizer.Lattice.EdgeIdx L,
              Stabilizer.Lattice.edgeToQubitIdx L e = q := by
            have h_edge :
                Finset.image (Stabilizer.Lattice.edgeToQubitIdx L)
                    (Finset.univ : Finset (Stabilizer.Lattice.EdgeIdx L)) = Finset.univ := by
              refine Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_
              rw [Finset.card_image_of_injective _ (Stabilizer.Lattice.edgeToQubitIdx_injective L)]
              simp +decide [Finset.card_univ]
            exact
              Finset.mem_image.mp (h_edge.symm ▸ Finset.mem_univ q) |>
                Exists.imp (fun x hx => hx.2)
          tauto
        · cases hgX.2 q <;> aesop
        · cases hgX.2 q <;> aesop
    exact this g hgX;
  have h_cycle :
      c ∈ Stabilizer.Lattice.toricCycles (L := L) ∧
        c ∉ Stabilizer.Lattice.toricBoundaries (L := L) := by
    rw [hc] at hgLogical;
    exact (Stabilizer.Lattice.xNontrivialLogical_iff_cycle_not_boundary L c).mp hgLogical;
  have h_weight : Stabilizer.Lattice.edgeWeight (L := L) c ≥ L := by
    have h_weight :
        Stabilizer.Lattice.hWrap (L := L) ⟨c, h_cycle.left⟩ ≠ 0 ∨
          Stabilizer.Lattice.vWrap (L := L) ⟨c, h_cycle.left⟩ ≠ 0 := by
      have h_weight :
          Stabilizer.Lattice.phi (L := L) (Submodule.Quotient.mk ⟨c, h_cycle.left⟩) ≠
            (0, 0) := by
        intro h
        have := Stabilizer.Lattice.phi_injective (L := L)
        simp_all +decide
        have := @this
          (Submodule.Quotient.mk ⟨c, h_cycle.1⟩)
          (Submodule.Quotient.mk ⟨0, by exact Submodule.zero_mem _⟩)
        simp_all +decide
        simp_all +decide [Stabilizer.Lattice.phi]
        simp_all +decide [Stabilizer.Lattice.hAt, Stabilizer.Lattice.vAt]
        rw [Submodule.Quotient.eq] at this
        aesop
      contrapose! h_weight
      aesop
    cases h_weight <;> simp_all +decide [Stabilizer.Lattice.hWrap, Stabilizer.Lattice.vWrap]
    · have h_weight : ∀ x : Fin L, ∑ y : Fin L,
          (if c (Stabilizer.Lattice.EdgeIdx.h x y) ≠ 0 then 1 else 0) ≥ 1 := by
        intro x
        have h_sum :
            ∑ y : Fin L, c (Stabilizer.Lattice.EdgeIdx.h x y) =
              ∑ y : Fin L, c (Stabilizer.Lattice.EdgeIdx.h (Stabilizer.Lattice.zeroCoord L) y) := by
          have := Stabilizer.Lattice.hAt_independent_on_cycles (L := L) ⟨c, h_cycle.1⟩ x
            (Stabilizer.Lattice.zeroCoord L)
          aesop
        contrapose! h_sum
        simp_all +decide [Finset.sum_ite]
        exact Ne.symm ‹_›
      have h_weight : ∑ x : Fin L, ∑ y : Fin L,
          (if c (Stabilizer.Lattice.EdgeIdx.h x y) ≠ 0 then 1 else 0) ≥ L := by
        exact le_trans ( by norm_num ) ( Finset.sum_le_sum fun x _ => h_weight x );
      refine le_trans h_weight ?_;
      unfold Stabilizer.Lattice.edgeWeight;
      rw [show Stabilizer.Lattice.edgeSupport c =
          Finset.image (fun p : Fin L × Fin L => Stabilizer.Lattice.EdgeIdx.h p.1 p.2)
            (Finset.filter (fun p : Fin L × Fin L => c (Stabilizer.Lattice.EdgeIdx.h p.1 p.2) ≠ 0)
              (Finset.univ : Finset (Fin L × Fin L)))
          ∪ Finset.image (fun p : Fin L × Fin L => Stabilizer.Lattice.EdgeIdx.v p.1 p.2)
            (Finset.filter (fun p : Fin L × Fin L => c (Stabilizer.Lattice.EdgeIdx.v p.1 p.2) ≠ 0)
              (Finset.univ : Finset (Fin L × Fin L))) from ?_]
      · rw [ Finset.card_union_of_disjoint ];
        · rw [Finset.card_image_of_injective, Finset.card_image_of_injective] <;>
            norm_num [Function.Injective]
          rw [Finset.card_filter, Finset.card_filter]
          rw [← Finset.sum_product']
          exact le_add_of_le_of_nonneg (Finset.sum_le_sum (fun _ _ => by aesop)) (Nat.zero_le _)
        · simp +decide [Finset.disjoint_left]
          grind
      · ext e
        simp [Stabilizer.Lattice.edgeSupport]
        cases e <;> simp +decide [*]
    · have h_weight :
          ∀ y : Fin L,
            (Finset.univ.filter
              (fun x : Fin L => c (Stabilizer.Lattice.EdgeIdx.v x y) ≠ 0)).card ≥ 1 := by
        intros y
        have h_sum :
            ∑ x : Fin L, c (Stabilizer.Lattice.EdgeIdx.v x y) =
              ∑ x : Fin L, c (Stabilizer.Lattice.EdgeIdx.v x (Stabilizer.Lattice.zeroCoord L)) := by
          have := Stabilizer.Lattice.vAt_independent_on_cycles (L := L) ⟨c, h_cycle.1⟩ y
            (Stabilizer.Lattice.zeroCoord L)
          aesop
        contrapose! h_sum
        simp_all +decide
        exact Ne.symm ‹_›
      have h_weight :
          (Finset.univ.filter (fun e : Stabilizer.Lattice.EdgeIdx L => c e ≠ 0)).card ≥
            (Finset.univ : Finset (Fin L)).sum
              (fun y =>
                (Finset.univ.filter
                  (fun x : Fin L => c (Stabilizer.Lattice.EdgeIdx.v x y) ≠ 0)).card) := by
        have h_weight :
            (Finset.univ.filter (fun e : Stabilizer.Lattice.EdgeIdx L => c e ≠ 0)).card ≥
              (Finset.univ.biUnion
                (fun y : Fin L =>
                  Finset.image (fun x : Fin L => Stabilizer.Lattice.EdgeIdx.v x y)
                    (Finset.univ.filter
                      (fun x : Fin L => c (Stabilizer.Lattice.EdgeIdx.v x y) ≠ 0)))).card := by
          refine Finset.card_le_card ?_
          grind +splitImp
        rw [Finset.card_biUnion] at h_weight
        · exact h_weight.trans'
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
              (fun y (hy : y ∈ Finset.univ) =>
                ‹∀ y : Fin L,
                    Finset.card
                      (Finset.filter
                        (fun x => c (Stabilizer.Lattice.EdgeIdx.v x y) ≠ 0) Finset.univ) ≥
                      1› y))
        h_weight
  rw [ hc ];
  refine le_trans h_weight ?_
  unfold Stabilizer.Lattice.toricXOperatorOfChain;
  unfold Stabilizer.Lattice.edgeWeight NQubitPauliGroupElement.weight;
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
  · exact fun b x hx hx' => ⟨ x, by aesop ⟩


/-- Section 8 endpoint scaffold: the toric X-distance is `L`. -/
theorem toricCodeN_hasXDistance_L (L : ℕ) [Fact (2 ≤ L)] :
    HasToricXDistance L L := by
  refine ⟨?_, ?_, ?_⟩
  · have hL : 2 ≤ L := Fact.out
    omega
  · intro g hgX hgLogical hgPos
    exact nontrivial_x_logical_weight_ge_L L g hgX hgLogical
  · exact exists_nontrivial_x_logical_weight_eq_L L

/-- Section 8 endpoint alias: `dX = L` for the toric code. -/
theorem toricCodeN_dX_eq_L (L : ℕ) [Fact (2 ≤ L)] :
    HasToricXDistance L L := by
  simpa using toricCodeN_hasXDistance_L L

-- ---------------------------------------------------------------------------
-- Vertical X-loop: the column-0 sister of `horizontalLoopChain`/`horizontalLoopXOperator`
-- ---------------------------------------------------------------------------

/-- Vertical X-loop chain: V-edges along column `x = zeroCoord`. -/
def verticalLoopChain (L : ℕ) [Fact (0 < L)] : Stabilizer.Lattice.C1 L :=
  fun e =>
    match e with
    | Stabilizer.Lattice.EdgeIdx.h _ _ => 0
    | Stabilizer.Lattice.EdgeIdx.v x _ =>
        if x = Stabilizer.Lattice.zeroCoord L then (1 : ZMod 2) else 0

/-- X-type Pauli operator encoded by the vertical loop chain. -/
def verticalLoopXOperator (L : ℕ) [Fact (0 < L)] :
    NQubitPauliGroupElement (Stabilizer.Lattice.toricNumQubits L) :=
  Stabilizer.Lattice.toricXOperatorOfChain L (verticalLoopChain L)

/-- The vertical X-loop chain is a primal cycle. -/
theorem verticalLoopChain_mem_toricCycles (L : ℕ) [Fact (2 ≤ L)] :
    verticalLoopChain L ∈ Stabilizer.Lattice.toricCycles (L := L) := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  unfold Stabilizer.Lattice.toricCycles
  rw [LinearMap.mem_ker]
  ext ⟨xv, yv⟩
  simp only [Stabilizer.Lattice.toricBoundary1, LinearMap.coe_mk, AddHom.coe_mk,
    verticalLoopChain]
  by_cases hx : xv = Stabilizer.Lattice.zeroCoord L
  · subst hx
    show (0 : ZMod 2) + 0 + 1 + 1 = 0
    decide
  · simp [hx]

/-- The vertical X-loop chain is not a primal boundary (its `vAt` invariant is 1). -/
theorem verticalLoopChain_not_mem_toricBoundaries (L : ℕ) [Fact (2 ≤ L)] :
    verticalLoopChain L ∉ Stabilizer.Lattice.toricBoundaries (L := L) := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  intro h
  have h_vAt : Stabilizer.Lattice.vAt (L := L) (Stabilizer.Lattice.zeroCoord L)
      (verticalLoopChain L) = 0 :=
    Stabilizer.Lattice.v_boundary_zero (L := L) ⟨verticalLoopChain L, h⟩
  have h_compute : Stabilizer.Lattice.vAt (L := L) (Stabilizer.Lattice.zeroCoord L)
      (verticalLoopChain L) = 1 := by
    unfold Stabilizer.Lattice.vAt verticalLoopChain
    rw [Finset.sum_eq_single (Stabilizer.Lattice.zeroCoord L)]
    · simp
    · intro b _ hbne
      simp [hbne]
    · intro hcontra; exact absurd (Finset.mem_univ _) hcontra
  rw [h_compute] at h_vAt
  exact absurd h_vAt (by decide)

/-- The vertical X-loop chain has edge weight `L`. -/
theorem verticalLoopChain_edgeWeight_eq_L (L : ℕ) [Fact (2 ≤ L)] :
    Stabilizer.Lattice.edgeWeight (L := L) (verticalLoopChain L) = L := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  let z0 : Fin L := Stabilizer.Lattice.zeroCoord L
  let vertCol : Finset (Stabilizer.Lattice.EdgeIdx L) :=
    (Finset.univ.image (fun y : Fin L => Stabilizer.Lattice.EdgeIdx.v z0 y))
  have hsupport :
      Stabilizer.Lattice.edgeSupport (L := L) (verticalLoopChain L) = vertCol := by
    ext e
    constructor
    · intro he
      have hne : verticalLoopChain L e ≠ 0 := by
        simpa [Stabilizer.Lattice.mem_edgeSupport] using he
      cases e with
      | h x y => simp [verticalLoopChain] at hne
      | v x y =>
          by_cases hx : x = z0
          · subst hx
            refine Finset.mem_image.mpr ?_
            exact ⟨y, Finset.mem_univ y, rfl⟩
          · have hx' : x = z0 := by simpa [verticalLoopChain] using hne
            exact (hx hx').elim
    · intro he
      rcases Finset.mem_image.mp he with ⟨y, -, hy⟩
      subst hy
      simp [Stabilizer.Lattice.mem_edgeSupport, verticalLoopChain, z0]
  have hinj : Function.Injective (fun y : Fin L => Stabilizer.Lattice.EdgeIdx.v z0 y) := by
    intro a b h; cases h; rfl
  have hcard : vertCol.card = L := by
    calc
      vertCol.card
          = (Finset.univ.image (fun y : Fin L => Stabilizer.Lattice.EdgeIdx.v z0 y)).card := rfl
      _ = (Finset.univ : Finset (Fin L)).card := by
          exact Finset.card_image_of_injective
            (s := (Finset.univ : Finset (Fin L)))
            (f := fun y : Fin L => Stabilizer.Lattice.EdgeIdx.v z0 y)
            (by intro a b hab; exact hinj hab)
      _ = L := by simp
  calc
    Stabilizer.Lattice.edgeWeight (L := L) (verticalLoopChain L)
        = (Stabilizer.Lattice.edgeSupport (L := L) (verticalLoopChain L)).card := rfl
    _ = vertCol.card := by rw [hsupport]
    _ = L := hcard

/-- The vertical X-loop operator is X-type. -/
theorem verticalLoopXOperator_isXType (L : ℕ) [Fact (0 < L)] :
    NQubitPauliGroupElement.IsXTypeElement (verticalLoopXOperator L) := by
  unfold verticalLoopXOperator NQubitPauliGroupElement.IsXTypeElement
  refine ⟨rfl, fun q => ?_⟩
  by_cases h : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧ verticalLoopChain L e = 1
  · right; simp [Stabilizer.Lattice.toricXOperatorOfChain, h]
  · left; simp [Stabilizer.Lattice.toricXOperatorOfChain, h]

/-- The horizontal X-loop operator is X-type. -/
theorem horizontalLoopXOperator_isXType (L : ℕ) [Fact (0 < L)] :
    NQubitPauliGroupElement.IsXTypeElement (horizontalLoopXOperator L) := by
  unfold horizontalLoopXOperator NQubitPauliGroupElement.IsXTypeElement
  refine ⟨rfl, fun q => ?_⟩
  by_cases h : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧ horizontalLoopChain L e = 1
  · right; simp [Stabilizer.Lattice.toricXOperatorOfChain, h]
  · left; simp [Stabilizer.Lattice.toricXOperatorOfChain, h]

end ToricCodeN
end StabilizerGroup
end Quantum
