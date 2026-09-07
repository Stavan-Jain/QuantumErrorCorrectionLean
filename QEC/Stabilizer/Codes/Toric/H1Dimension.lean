import Mathlib.Tactic
import QEC.Stabilizer.Codes.Toric.Homology
import QEC.Stabilizer.Framework.Homological.Code


namespace Quantum
namespace Stabilizer
namespace Lattice

open scoped BigOperators
open scoped Homology
open scoped ToricChain

variable (L : ℕ) [Fact (0 < L)]

/-- The boundary submodule viewed inside the cycle submodule (`B₁` as a submodule of `Z₁`). -/
abbrev toricBoundarySubmoduleInCycles : Submodule (ZMod 2) (Z₁ L) :=
  Submodule.comap (Z₁ L).subtype (B₁ L)

/-- Finrank of the toric 0-chain space. -/
theorem toric_finrank_C0 :
    dim₂ (C0 L) = L * L := by
  let _ := (Fact.out : 0 < L)
  calc
    dim₂ (C0 L) = Fintype.card (VtxIdx L) := by
      exact Module.finrank_fintype_fun_eq_card (R := ZMod 2) (η := VtxIdx L)
    _ = L * L := by simp

/-- Finrank of the toric 1-chain space. -/
theorem toric_finrank_C1 :
    dim₂ (C1 L) = 2 * L * L := by
  let _ := (Fact.out : 0 < L)
  calc
    dim₂ (C1 L) = Fintype.card (EdgeIdx L) := by
      exact Module.finrank_fintype_fun_eq_card (R := ZMod 2) (η := EdgeIdx L)
    _ = 2 * L * L := by simp

/-- Finrank of the toric 2-chain space. -/
theorem toric_finrank_C2 :
    dim₂ (C2 L) = L * L := by
  let _ := (Fact.out : 0 < L)
  calc
    dim₂ (C2 L) = Fintype.card (FaceIdx L) := by
      exact Module.finrank_fintype_fun_eq_card (R := ZMod 2) (η := FaceIdx L)
    _ = L * L := by simp

/-- `B₁ ≤ Z₁` for the toric chain complex. -/
theorem toric_boundaries_le_cycles :
    B₁ L ≤ Z₁ L := by
  simpa using toricBoundaries_le_toricCycles L

/-- Rank-nullity specialization for `∂₁`. -/
theorem toric_rank_nullity_boundary1 :
    dim₂ (C1 L) =
      dim₂ (Z₁ L) +
        dim₂ (LinearMap.range (∂₁ (L := L))) := by
  simpa [toricCycles, add_comm, add_left_comm, add_assoc] using
    (LinearMap.finrank_range_add_finrank_ker (∂₁ (L := L))).symm

/-- Rank-nullity specialization for `∂₂`. -/
theorem toric_rank_nullity_boundary2 :
    dim₂ (C2 L) =
      dim₂ (LinearMap.ker (∂₂ (L := L))) +
        dim₂ (B₁ L) := by
  simpa [toricBoundaries, add_comm, add_left_comm, add_assoc] using
    (LinearMap.finrank_range_add_finrank_ker (∂₂ (L := L))).symm

/-- The vertex cut map: sends a 0-chain `s` to the 1-chain whose value at edge `e`
is the parity-difference of `s` at the two endpoints of `e`. This is the transpose
of `∂₁` and the linear map whose image is exactly the `B₁` boundary subspace, used
to compute `rank(∂₁)` via `toric_rank_boundary1_eq_rank_cutMap`. -/
noncomputable def toricVertexCutMap : C0 L →ₗ[ZMod 2] C1 L := by
  refine
    { toFun := fun s =>
        fun e =>
          match e with
          | EdgeIdx.h x y => s (x, y) + s (next L x, y)
          | EdgeIdx.v x y => s (x, y) + s (x, next L y)
      map_add' := ?_
      map_smul' := ?_ }
  · intro s t
    ext e
    cases e <;> simp [add_assoc, add_left_comm, add_comm]
  · intro a s
    ext e
    cases e <;> simp [mul_add]

/-- `δ⁰` is the toric vertex cut map `toricVertexCutMap : C0 L →ₗ[ZMod 2] C1 L` (the
transpose of `∂₁`, i.e. the coboundary `C⁰ → C¹`), with the lattice size explicit:
`δ⁰ L s`. Scoped: `open scoped ToricChain`. -/
scoped[ToricChain] notation "δ⁰" => Quantum.Stabilizer.Lattice.toricVertexCutMap

/-
The pairing ⟨∂₁ c, s⟩ = ⟨c, cutMap s⟩, showing ∂₁ and cutMap are transposes.
-/
set_option maxHeartbeats 400000 in
-- This transpose-expansion proof is algebra-heavy and needs extra heartbeats.
theorem toricBoundary1_cutMap_transpose (c : C1 L) (s : C0 L) :
    ∑ v : VtxIdx L, ∂₁ (L := L) c v * s v =
    ∑ e : EdgeIdx L, c e * δ⁰ (L := L) s e := by
  -- Expand both sides using the definitions.
  have h_expand_lhs :
      ∑ v : Fin L × Fin L, (∂₁ L c v) * s v =
        ∑ v : Fin L × Fin L,
          (c (EdgeIdx.h v.1 v.2) + c (EdgeIdx.h (prev L v.1) v.2) +
            c (EdgeIdx.v v.1 v.2) + c (EdgeIdx.v v.1 (prev L v.2))) * s v := by
    rfl
  generalize_proofs at *; (
  have h_expand_rhs :
      ∑ e : EdgeIdx L, c e * (δ⁰ L s e) =
        ∑ x : Fin L, ∑ y : Fin L,
          (c (EdgeIdx.h x y) * (s (x, y) + s (next L x, y)) +
            c (EdgeIdx.v x y) * (s (x, y) + s (x, next L y))) := by
    rw [ ← Finset.sum_product' ];
    rw [← Finset.sum_subset
      (Finset.subset_univ
        (Finset.image (fun x : Fin L × Fin L => EdgeIdx.h x.1 x.2) (Finset.univ ×ˢ Finset.univ) ∪
          Finset.image (fun x : Fin L × Fin L => EdgeIdx.v x.1 x.2) (Finset.univ ×ˢ Finset.univ)))];
    · rw [ Finset.sum_union ];
      · rw [ Finset.sum_image, Finset.sum_image ] <;> simp +decide [ Finset.sum_add_distrib ]
        · rfl
        · exact fun a b hab => by cases a; cases b; simp_all [EdgeIdx.v.injEq]
        · exact fun a b hab => by cases a; cases b; simp_all [EdgeIdx.h.injEq]
      · simp +decide [ Finset.disjoint_left ];
        aesop;
    · intro x hx hx'; rcases x with ( _ | _ ) <;> simp +decide at hx' ⊢;
  generalize_proofs at *; (
  -- By reindexing the sums, we can see that they are equal.
  have h_reindex :
      (∑ x : Fin L, ∑ y : Fin L, c (EdgeIdx.h x y) * s (next L x, y)) =
        (∑ x : Fin L, ∑ y : Fin L, c (EdgeIdx.h (prev L x) y) * s (x, y)) ∧
      (∑ x : Fin L, ∑ y : Fin L, c (EdgeIdx.v x y) * s (x, next L y)) =
        (∑ x : Fin L, ∑ y : Fin L, c (EdgeIdx.v x (prev L y)) * s (x, y)) := by
    constructor <;>
      rw [← Equiv.sum_comp
        (Equiv.ofBijective (prev L) ⟨fun x y hxy => ?_, fun x => ?_⟩)] <;>
      norm_num [add_comm, add_left_comm, add_assoc]
    · have := prev_next L x; have := prev_next L y; aesop;
    · -- Reindex using that `prev L` is a bijection.
      have h_reindex :
          ∀ x : Fin L,
            ∑ y : Fin L, c (EdgeIdx.v x (prev L y)) * s (x, y) =
              ∑ y : Fin L, c (EdgeIdx.v x y) * s (x, next L y) := by
        intro x
        rw [← Equiv.sum_comp
          (Equiv.ofBijective (fun y : Fin L => next L y) ⟨fun x y hxy => ?_, fun x => ?_⟩)]
        · norm_num [prev_next, next_prev]
        · exact prev_next L x ▸ prev_next L y ▸ congr_arg (fun z => prev L z) hxy ▸ rfl
        · exact ⟨ prev L x, by simp +decide [ next_prev ] ⟩
      generalize_proofs at *; (
      rw [← Equiv.sum_comp
        (Equiv.ofBijective (fun x : Fin L => next L x) ⟨fun x y hxy => ?_, fun x => ?_⟩)] <;>
        norm_num [next_prev, prev_next]
      · exact Finset.sum_congr rfl fun _ _ => h_reindex _ ▸ rfl;
      · exact prev_next L x ▸ prev_next L y ▸ congr_arg ( fun z => prev L z ) hxy ▸ rfl;
      · exact ⟨ prev L x, by simp +decide [ next_prev ] ⟩);
    · have := prev_next L x; have := prev_next L y; aesop;
  generalize_proofs at *; (
  simp_all +decide [ Finset.sum_add_distrib, mul_add, add_mul ];
  simp +decide only [← Finset.sum_product'] ; ring!;)))

/-- `∂₁` and `toricVertexCutMap` are mutual transposes, so they have equal rank. -/
theorem toric_rank_boundary1_eq_rank_cutMap :
    dim₂ (LinearMap.range (∂₁ (L := L))) =
      dim₂ (LinearMap.range (δ⁰ (L := L))) := by
  rw [ ← LinearMap.finrank_range_dualMap_eq_finrank_range ];
  fapply LinearEquiv.finrank_eq;
  symm;
  refine LinearEquiv.ofBijective ?_ ⟨?_, ?_⟩
  · refine { toFun := ?_, map_add' := ?_, map_smul' := ?_ }
    · refine fun x => ⟨?_, ?_⟩
      · refine { toFun := fun c => ∑ e : EdgeIdx L, c e * x.val e,
                 map_add' := ?_, map_smul' := ?_ }
        all_goals
          norm_num
            [funext_iff, Finset.sum_add_distrib, mul_add, add_mul, mul_assoc, mul_left_comm,
              Finset.mul_sum _ _ _]
      · obtain ⟨ y, hy ⟩ := x.2
        refine ⟨?_, ?_⟩
        · exact ∑ v : VtxIdx L, y v • ( LinearMap.proj v )
        · ext c
          simp +decide [ ← hy ]
          convert toricBoundary1_cutMap_transpose L ( Pi.single c 1 ) y using 1
          ac_rfl
    all_goals
      norm_num
        [funext_iff, Finset.sum_add_distrib, mul_add, add_mul, mul_assoc, mul_left_comm,
          Finset.mul_sum _ _ _]
    any_goals intros; ext; simp +decide [ Finset.mul_sum _ _ _ ]
  all_goals norm_num [ Function.Injective, Function.Surjective ]
  · intro a b h
    ext x
    replace h := congr_fun h (fun y => if y = x then 1 else 0)
    aesop
  · intro a
    refine ⟨_, ⟨fun v => a (fun u => if u = v then 1 else 0), rfl⟩, ?_⟩
    ext c; simp +decide
    convert (toricBoundary1_cutMap_transpose L (Pi.single c 1)
      (fun v => a (fun u => if u = v then 1 else 0))).symm using 1
    convert a.pi_apply_eq_sum_univ _ using 1
    simp +decide [ eq_comm, mul_comm ]

/-- The kernel of the toric vertex cut map consists exactly of the constant 0-chains. -/
theorem mem_ker_cutMap_iff (s : C0 L) :
    s ∈ LinearMap.ker (δ⁰ (L := L)) ↔ ∃ c : ZMod 2, s = fun _ => c := by
  constructor
  · intro hs
    have h_const : ∀ x y : Fin L, s (x, y) = s (next L x, y) ∧ s (x, y) = s (x, next L y) := by
      intro x y
      have h_eq :
          s (x, y) + s (next L x, y) = 0 ∧ s (x, y) + s (x, next L y) = 0 := by
        exact ⟨by simpa using congr_fun hs (EdgeIdx.h x y),
          by simpa using congr_fun hs (EdgeIdx.v x y)⟩
      grind +splitImp
    have h_const_val : ∃ c : ZMod 2, ∀ x y : Fin L, s (x, y) = c := by
      use s (⟨0, by linarith [Fact.out (p := 0 < L)]⟩, ⟨0, by linarith [Fact.out (p := 0 < L)]⟩);
      intro x y
      have h_const_x : ∀ x : Fin L, s (x, y) = s (⟨0, by linarith [Fact.out (p := 0 < L)]⟩, y) := by
        intro x
        have h_const_x_step :
            ∀ k : ℕ,
              s (⟨(k % L), Nat.mod_lt _ (Fact.out (p := 0 < L))⟩, y) =
                s (⟨0, by linarith [Fact.out (p := 0 < L)]⟩, y) := by
          intro k
          induction k with
          | zero =>
              generalize_proofs at *
              norm_num [Nat.mod_eq_of_lt]
          | succ k ih =>
              generalize_proofs at *
              specialize h_const ⟨k % L, by linarith⟩ y
              unfold next at h_const
              aesop
        simpa [ Nat.mod_eq_of_lt x.2 ] using h_const_x_step x.1
      have h_const_y :
          ∀ y : Fin L,
            s (⟨0, by linarith [Fact.out (p := 0 < L)]⟩, y) =
              s (⟨0, by linarith [Fact.out (p := 0 < L)]⟩,
                ⟨0, by linarith [Fact.out (p := 0 < L)]⟩) := by
        intro y
        obtain ⟨y, ih⟩ := y
        induction y with
        | zero => rfl
        | succ y ih_step =>
            specialize h_const
              ⟨0, by linarith [Fact.out (p := 0 < L)]⟩
              ⟨y, by linarith [Fact.out (p := 0 < L)]⟩
            simp_all +decide [ next ]
            simp_all +decide [ Nat.mod_eq_of_lt ( by linarith : y + 1 < L ) ]
            grind
      exact h_const_x x ▸ h_const_y y ▸ rfl
    obtain ⟨c, hc⟩ := h_const_val
    exact ⟨c, funext fun p => by simp [hc]⟩
  · rintro ⟨ c, rfl ⟩
    rw [LinearMap.mem_ker]
    ext e
    cases e <;> simp +decide
    · exact show c + c = 0 from by fin_cases c <;> rfl
    · exact show (c + c : ZMod 2) = 0 from by have := Fin.exists_fin_two.mp ⟨c, rfl⟩; aesop

/-- The kernel of the toric vertex cut map equals `span{constant 1}`. -/
theorem ker_toricVertexCutMap_eq_span_one :
    LinearMap.ker (δ⁰ (L := L)) =
      Submodule.span (ZMod 2) ({fun _ => 1} : Set (C0 L)) := by
  ext s
  rw [mem_ker_cutMap_iff, Submodule.mem_span_singleton]
  exact ⟨
    (fun ⟨c, hc⟩ => ⟨c, hc ▸ by ext; simp +decide⟩),
    (fun ⟨c, hc⟩ => ⟨c, hc ▸ by ext; simp +decide⟩)⟩

/-- Kernel-dimension result for the cut-map connectivity argument. -/
theorem toric_finrank_ker_cutMap_eq_one :
    dim₂ (LinearMap.ker (δ⁰ (L := L))) = 1 := by
  rw [ker_toricVertexCutMap_eq_span_one, finrank_span_singleton]
  exact fun h => by simpa using congr_fun h (⟨0, Fact.out⟩, ⟨0, Fact.out⟩)

/-- Target rank formula for `∂₁`. -/
theorem toric_rank_boundary1 :
    dim₂ (LinearMap.range (∂₁ (L := L))) = L * L - 1 := by
  have hcut_rk :
      dim₂ (LinearMap.range (δ⁰ (L := L))) = L * L - 1 := by
    have hcut_rn := LinearMap.finrank_range_add_finrank_ker (δ⁰ (L := L))
    have hC0 := toric_finrank_C0 L
    have hker := toric_finrank_ker_cutMap_eq_one L
    omega
  have hbridge := toric_rank_boundary1_eq_rank_cutMap L
  omega

/-- Target cycle-space dimension formula. -/
theorem toric_finrank_cycles :
    dim₂ (Z₁ L) = L * L + 1 := by
  have hrn := toric_rank_nullity_boundary1 L
  have hC1 := toric_finrank_C1 L
  have hrk := toric_rank_boundary1 L
  rw [hC1, hrk] at hrn
  have hEq : dim₂ (Z₁ L) + (L * L - 1) = 2 * L * L := by
    simpa [add_comm, add_left_comm, add_assoc] using hrn.symm
  have hsq : 1 ≤ L * L := by
    have hL : 0 < L := Fact.out
    exact Nat.succ_le_of_lt (Nat.mul_pos hL hL)
  have hsplit : (L * L + 1) + (L * L - 1) = 2 * L * L := by
    calc
      (L * L + 1) + (L * L - 1) = ((L * L - 1) + 1) + (L * L) := by
        ac_rfl
      _ = (L * L) + (L * L) := by
        rw [Nat.sub_add_cancel hsq]
      _ = 2 * L * L := by ring
  have : dim₂ (Z₁ L) + (L * L - 1) =
      (L * L + 1) + (L * L - 1) := by
    exact hEq.trans hsplit.symm
  exact Nat.add_right_cancel this

/-- The kernel of `∂₂` consists exactly of the constant 2-chains. -/
theorem mem_ker_boundary2_iff (f : C2 L) :
    f ∈ LinearMap.ker (∂₂ (L := L)) ↔ ∃ c : ZMod 2, f = fun _ => c := by
  constructor
  · intro hf
    have h_const : ∀ x y, f (x, next L y) = f (x, y) := by
      intro x y
      have := congr_fun hf (EdgeIdx.h x (next L y))
      simp_all +decide [toricBoundary2]
      rw [eq_neg_of_add_eq_zero_left this,
        neg_eq_of_add_eq_zero_right
          (show f (x, y) + f (x, y) = 0 from by
            rw [← two_smul (ZMod 2) _]
            simp +decide)]
    have h_ind : ∀ x y, f (x, y) = f (x, ⟨0, by linarith [Fact.out (p := 0 < L)]⟩) := by
      intro x y
      obtain ⟨y, ih⟩ := y
      induction y with
      | zero => rfl
      | succ y ih_step =>
          convert h_const x ⟨ y, by linarith ⟩ using 1
          · congr
            norm_num [ Fin.val_add, Nat.mod_eq_of_lt ih ]
          · exact Eq.symm ( by solve_by_elim [ Nat.lt_of_succ_lt ] )
    have h_const_x :
        ∀ x, f (next L x, ⟨0, by linarith [Fact.out (p := 0 < L)]⟩) =
          f (x, ⟨0, by linarith [Fact.out (p := 0 < L)]⟩) := by
      intro x
      have h_eq :
          f (x, ⟨0, by linarith [Fact.out (p := 0 < L)]⟩) +
            f (prev L x, ⟨0, by linarith [Fact.out (p := 0 < L)]⟩) = 0 := by
        convert congr_arg
          (fun g => g (EdgeIdx.v x ⟨0, by linarith [Fact.out (p := 0 < L)]⟩)) hf using 1
      have h_eq :
          f (next L x, ⟨0, by linarith [Fact.out (p := 0 < L)]⟩) +
            f (x, ⟨0, by linarith [Fact.out (p := 0 < L)]⟩) = 0 := by
        have := hf
        simp_all +decide [toricBoundary2]
        have := congr_fun hf (EdgeIdx.v (next L x) ⟨0, by linarith [Fact.out (p := 0 < L)]⟩)
        simp +decide at this
        exact this
      grind;
    have h_ind_x :
        ∀ x, f (x, ⟨0, by linarith [Fact.out (p := 0 < L)]⟩) =
          f (⟨0, by linarith [Fact.out (p := 0 < L)]⟩,
            ⟨0, by linarith [Fact.out (p := 0 < L)]⟩) := by
      intro x
      obtain ⟨x, ih⟩ := x
      induction x with
      | zero => rfl
      | succ x ih_step =>
          convert h_const_x ⟨ x, by linarith ⟩ using 1
          · exact Fin.ext ( by simp +decide [ next, Nat.mod_eq_of_lt ih ] )
          · exact Eq.symm ( by solve_by_elim [ Nat.lt_of_succ_lt ] )
    exact
      ⟨f (⟨0, by linarith [Fact.out (p := 0 < L)]⟩, ⟨0, by linarith [Fact.out (p := 0 < L)]⟩),
        funext fun x => by aesop⟩
  · rintro ⟨c, rfl⟩
    rw [LinearMap.mem_ker]
    ext e
    cases e <;> simp +decide [toricBoundary2]
    · exact show (c + c : ZMod 2) = 0 from by have := Fin.exists_fin_two.mp ⟨c, rfl⟩; aesop
    · exact show (c + c : ZMod 2) = 0 from by have := Fin.exists_fin_two.mp ⟨c, rfl⟩; aesop

/-- The kernel of `∂₂` equals `span{constant 1}`. -/
theorem ker_toricBoundary2_eq_span_one :
    LinearMap.ker (∂₂ (L := L)) =
      Submodule.span (ZMod 2) ({fun _ => 1} : Set (C2 L)) := by
  ext f
  rw [mem_ker_boundary2_iff, Submodule.mem_span_singleton]
  exact ⟨
    (fun ⟨c, hc⟩ => ⟨c, hc ▸ by ext; simp +decide⟩),
    (fun ⟨c, hc⟩ => ⟨c, hc ▸ by ext; simp +decide⟩)⟩

/-- Kernel-dimension result for `∂₂`. -/
theorem toric_finrank_ker_boundary2_eq_one :
    dim₂ (LinearMap.ker (∂₂ (L := L))) = 1 := by
  rw [ker_toricBoundary2_eq_span_one, finrank_span_singleton]
  exact fun h => by simpa using congr_fun h (⟨0, Fact.out⟩, ⟨0, Fact.out⟩)

/-- Target boundary-space dimension formula. -/
theorem toric_finrank_boundaries :
    dim₂ (B₁ L) = L * L - 1 := by
  have hrn := toric_rank_nullity_boundary2 L
  have hC2 := toric_finrank_C2 L
  have hker := toric_finrank_ker_boundary2_eq_one L
  omega

/-- Quotient-dimension bridge for `H₁ = Z₁ / B₁`. -/
theorem toric_finrank_H1_eq_cycles_sub_boundaries
    :
    @Module.finrank (ZMod 2) (H₁ L) _
      (Submodule.Quotient.addCommGroup (toricBoundarySubmoduleInCycles L)).toAddCommMonoid
      (Submodule.Quotient.module (toricBoundarySubmoduleInCycles L)) =
      dim₂ (Z₁ L) -
        dim₂ (B₁ L) := by
  have hquot :
      @Module.finrank (ZMod 2) (H₁ L) _
          (Submodule.Quotient.addCommGroup
            (toricBoundarySubmoduleInCycles L)).toAddCommMonoid
          (Submodule.Quotient.module (toricBoundarySubmoduleInCycles L)) +
          dim₂ (toricBoundarySubmoduleInCycles L) =
        dim₂ (Z₁ L) := by
    simpa [toricH1, toricBoundarySubmoduleInCycles] using
      (Submodule.finrank_quotient_add_finrank (R := ZMod 2)
        (toricBoundarySubmoduleInCycles L))
  have hcomap :
      dim₂ (toricBoundarySubmoduleInCycles L) =
        dim₂ (B₁ L) := by
    simpa [toricBoundarySubmoduleInCycles] using
      (Submodule.comapSubtypeEquivOfLe (toric_boundaries_le_cycles L)).finrank_eq
  rw [hcomap] at hquot
  exact Nat.eq_sub_of_add_eq hquot

/-- `dim(H₁) = 2` for the toric chain complex over `ZMod 2`. -/
theorem toric_finrank_H1_eq_two
    :
    @Module.finrank (ZMod 2) (H₁ L) _
      (Submodule.Quotient.addCommGroup (toricBoundarySubmoduleInCycles L)).toAddCommMonoid
      (Submodule.Quotient.module (toricBoundarySubmoduleInCycles L)) = 2 := by
  have hH := toric_finrank_H1_eq_cycles_sub_boundaries L
  have hC := toric_finrank_cycles L
  have hB := toric_finrank_boundaries L
  rw [hC, hB] at hH
  have hsq : 1 ≤ L * L := by
    have hL : 0 < L := Fact.out
    exact Nat.succ_le_of_lt (Nat.mul_pos hL hL)
  have hcalc : (L * L + 1) - (L * L - 1) = 2 := by
    omega
  simpa [hcalc] using hH

end Lattice
end Stabilizer
end Quantum
