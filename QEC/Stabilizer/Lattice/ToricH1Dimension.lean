import Mathlib.Tactic
import QEC.Stabilizer.Lattice.ToricHomology


namespace Quantum
namespace Stabilizer
namespace Lattice

open scoped BigOperators

variable (L : ℕ) [Fact (0 < L)]

/-- The boundary submodule viewed inside the cycle submodule (`B₁` as a submodule of `Z₁`). -/
abbrev toricBoundarySubmoduleInCycles : Submodule (ZMod 2) (toricCycles (L := L)) :=
  Submodule.comap (toricCycles (L := L)).subtype (toricBoundaries (L := L))

/-- Finrank of the toric 0-chain space. -/
theorem toric_finrank_C0 :
    Module.finrank (ZMod 2) (C0 L) = L * L := by
  let _ := (Fact.out : 0 < L)
  calc
    Module.finrank (ZMod 2) (C0 L) = Fintype.card (VtxIdx L) := by
      exact Module.finrank_fintype_fun_eq_card (R := ZMod 2) (η := VtxIdx L)
    _ = L * L := by simp

/-- Finrank of the toric 1-chain space. -/
theorem toric_finrank_C1 :
    Module.finrank (ZMod 2) (C1 L) = 2 * L * L := by
  let _ := (Fact.out : 0 < L)
  calc
    Module.finrank (ZMod 2) (C1 L) = Fintype.card (EdgeIdx L) := by
      exact Module.finrank_fintype_fun_eq_card (R := ZMod 2) (η := EdgeIdx L)
    _ = 2 * L * L := by simp

/-- Finrank of the toric 2-chain space. -/
theorem toric_finrank_C2 :
    Module.finrank (ZMod 2) (C2 L) = L * L := by
  let _ := (Fact.out : 0 < L)
  calc
    Module.finrank (ZMod 2) (C2 L) = Fintype.card (FaceIdx L) := by
      exact Module.finrank_fintype_fun_eq_card (R := ZMod 2) (η := FaceIdx L)
    _ = L * L := by simp

/-- `B₁ ≤ Z₁` for the toric chain complex. -/
theorem toric_boundaries_le_cycles :
    toricBoundaries (L := L) ≤ toricCycles (L := L) := by
  simpa using toricBoundaries_le_toricCycles (L := L)

/-- Rank-nullity specialization for `∂₁`. -/
theorem toric_rank_nullity_boundary1 :
    Module.finrank (ZMod 2) (C1 L) =
      Module.finrank (ZMod 2) (toricCycles (L := L)) +
        Module.finrank (ZMod 2) (LinearMap.range (toricBoundary1 (L := L))) := by
  simpa [toricCycles, add_comm, add_left_comm, add_assoc] using
    (LinearMap.finrank_range_add_finrank_ker (toricBoundary1 (L := L))).symm

/-- Rank-nullity specialization for `∂₂`. -/
theorem toric_rank_nullity_boundary2 :
    Module.finrank (ZMod 2) (C2 L) =
      Module.finrank (ZMod 2) (LinearMap.ker (toricBoundary2 (L := L))) +
        Module.finrank (ZMod 2) (toricBoundaries (L := L)) := by
  simpa [toricBoundaries, add_comm, add_left_comm, add_assoc] using
    (LinearMap.finrank_range_add_finrank_ker (toricBoundary2 (L := L))).symm

/-- Auxiliary map placeholder for the transpose/cut-map route used to compute `rank(∂₁)`. -/
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

/-
The pairing ⟨∂₁ c, s⟩ = ⟨c, cutMap s⟩, showing ∂₁ and cutMap are transposes.
-/
set_option maxHeartbeats 400000 in
-- This transpose-expansion proof is algebra-heavy and needs extra heartbeats.
theorem toricBoundary1_cutMap_transpose (c : C1 L) (s : C0 L) :
    ∑ v : VtxIdx L, toricBoundary1 (L := L) c v * s v =
    ∑ e : EdgeIdx L, c e * toricVertexCutMap (L := L) s e := by
  -- Expand both sides using the definitions.
  have h_expand_lhs :
      ∑ v : Fin L × Fin L, (toricBoundary1 L c v) * s v =
        ∑ v : Fin L × Fin L,
          (c (EdgeIdx.h v.1 v.2) + c (EdgeIdx.h (prev L v.1) v.2) +
            c (EdgeIdx.v v.1 v.2) + c (EdgeIdx.v v.1 (prev L v.2))) * s v := by
    rfl
  generalize_proofs at *; (
  have h_expand_rhs :
      ∑ e : EdgeIdx L, c e * (toricVertexCutMap L s e) =
        ∑ x : Fin L, ∑ y : Fin L,
          (c (EdgeIdx.h x y) * (s (x, y) + s (next L x, y)) +
            c (EdgeIdx.v x y) * (s (x, y) + s (x, next L y))) := by
    rw [ ← Finset.sum_product' ];
    rw [← Finset.sum_subset
      (Finset.subset_univ
        (Finset.image (fun x : Fin L × Fin L => EdgeIdx.h x.1 x.2) (Finset.univ ×ˢ Finset.univ) ∪
          Finset.image (fun x : Fin L × Fin L => EdgeIdx.v x.1 x.2) (Finset.univ ×ˢ Finset.univ)))];
    · rw [ Finset.sum_union ];
      · rw [ Finset.sum_image, Finset.sum_image ] <;> simp +decide [ Finset.sum_add_distrib ];
        · rfl;
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
        norm_num [prev_next, next_prev]
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

/-- Bridge theorem placeholder between `∂₁` rank and cut-map rank. -/
theorem toric_rank_boundary1_eq_rank_cutMap :
    Module.finrank (ZMod 2) (LinearMap.range (toricBoundary1 (L := L))) =
      Module.finrank (ZMod 2) (LinearMap.range (toricVertexCutMap (L := L))) := by
  rw [ ← LinearMap.finrank_range_dualMap_eq_finrank_range ];
  fapply LinearEquiv.finrank_eq;
  symm;
  refine' ( LinearEquiv.ofBijective _ ⟨ _, _ ⟩ );
  refine' { .. };
  refine' fun x => ⟨ _, _ ⟩;
  refine' { toFun := fun c => ∑ e : EdgeIdx L, c e * x.val e, map_add' := _, map_smul' := _ };
  all_goals
    norm_num
      [funext_iff, Finset.sum_add_distrib, mul_add, add_mul, mul_assoc, mul_left_comm,
        Finset.mul_sum _ _ _];
  any_goals intros; ext; simp +decide [ Finset.mul_sum _ _ _ ];
  all_goals norm_num [ Function.Injective, Function.Surjective ];
  · obtain ⟨ y, hy ⟩ := x.2;
    refine' ⟨ _, _ ⟩;
    exact ∑ v : VtxIdx L, y v • ( LinearMap.proj v );
    ext c; simp +decide [ ← hy ] ;
    convert toricBoundary1_cutMap_transpose L ( Pi.single c 1 ) y using 1;
    ac_rfl;
  · intro a b h
    ext x
    replace h := congr_fun h (fun y => if y = x then 1 else 0)
    aesop
  · intro a;
    refine' ⟨ _, ⟨ _, rfl ⟩, _ ⟩;
    exact fun v => a ( fun u => if u = v then 1 else 0 );
    ext c; simp +decide ;
    convert (toricBoundary1_cutMap_transpose L (Pi.single c 1)
      (fun v => a (fun u => if u = v then 1 else 0))).symm using 1;
    convert a.pi_apply_eq_sum_univ _ using 1;
    simp +decide [ eq_comm, mul_comm ]

/-- Kernel-dimension placeholder for the cut-map connectivity argument. -/
theorem toric_finrank_ker_cutMap_eq_one :
    Module.finrank (ZMod 2) (LinearMap.ker (toricVertexCutMap (L := L))) = 1 := by
  have h_span :
      ∀ s : C0 L, s ∈ LinearMap.ker (toricVertexCutMap (L := L)) ↔
        ∃ c : ZMod 2, s = fun _ => c := by
    intro s
    constructor
    intro hs
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
        induction' y with y ih;
        induction' y with y ih;
        · rfl;
        · specialize h_const
            ⟨0, by linarith [Fact.out (p := 0 < L)]⟩
            ⟨y, by linarith [Fact.out (p := 0 < L)]⟩
          simp_all +decide [ next ];
          simp_all +decide [ Nat.mod_eq_of_lt ( by linarith : y + 1 < L ) ];
          grind
      exact h_const_x x ▸ h_const_y y ▸ rfl
    obtain ⟨c, hc⟩ := h_const_val
    use c
    funext p
    simp [hc];
    rintro ⟨ c, rfl ⟩ ; ext e; cases e <;> simp +decide ;
    · exact show c + c = 0 from by fin_cases c <;> rfl;
    · exact show ( c + c : ZMod 2 ) = 0 from by have := Fin.exists_fin_two.mp ⟨ c, rfl ⟩ ; aesop;
  rw [show LinearMap.ker (toricVertexCutMap L) =
      Submodule.span (ZMod 2) {fun _ => 1} from _]
  · rw [ finrank_span_singleton ] ; norm_num;
    exact fun h => by simpa using congr_fun h ( ⟨ 0, Fact.out ⟩, ⟨ 0, Fact.out ⟩ ) ;
  · ext s; specialize h_span s; simp_all +decide [ Submodule.mem_span_singleton ] ;
    exact ⟨
      (fun ⟨c, hc⟩ => ⟨c, hc ▸ by ext; simp +decide⟩),
      (fun ⟨c, hc⟩ => ⟨c, hc ▸ by ext; simp +decide⟩)
    ⟩

/-- Target rank formula for `∂₁`. -/
theorem toric_rank_boundary1 :
    Module.finrank (ZMod 2) (LinearMap.range (toricBoundary1 (L := L))) = L * L - 1 := by
  have hcut_rk :
      Module.finrank (ZMod 2) (LinearMap.range (toricVertexCutMap (L := L))) = L * L - 1 := by
    have hcut_rn := LinearMap.finrank_range_add_finrank_ker (toricVertexCutMap (L := L))
    have hC0 := toric_finrank_C0 (L := L)
    have hker := toric_finrank_ker_cutMap_eq_one (L := L)
    omega
  have hbridge := toric_rank_boundary1_eq_rank_cutMap (L := L)
  omega

/-- Target cycle-space dimension formula. -/
theorem toric_finrank_cycles :
    Module.finrank (ZMod 2) (toricCycles (L := L)) = L * L + 1 := by
  have hrn := toric_rank_nullity_boundary1 (L := L)
  have hC1 := toric_finrank_C1 (L := L)
  have hrk := toric_rank_boundary1 (L := L)
  rw [hC1, hrk] at hrn
  have hEq : Module.finrank (ZMod 2) (toricCycles (L := L)) + (L * L - 1) = 2 * L * L := by
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
  have : Module.finrank (ZMod 2) (toricCycles (L := L)) + (L * L - 1) =
      (L * L + 1) + (L * L - 1) := by
    exact hEq.trans hsplit.symm
  exact Nat.add_right_cancel this

/-- Kernel-dimension placeholder for `∂₂`. -/
theorem toric_finrank_ker_boundary2_eq_one :
    Module.finrank (ZMod 2) (LinearMap.ker (toricBoundary2 (L := L))) = 1 := by
  have h_span :
      ∀ f ∈ LinearMap.ker (toricBoundary2 (L := L)), ∃ c : ZMod 2, f = fun _ => c := by
    intro f hf
    have h_const : ∀ x y, f (x, next L y) = f (x, y) := by
      intro x y
      have := congr_fun hf (EdgeIdx.h x (next L y))
      simp_all +decide [toricBoundary2]
      rw [eq_neg_of_add_eq_zero_left this,
        neg_eq_of_add_eq_zero_right
          (show f (x, y) + f (x, y) = 0 from by
            rw [← two_smul (ZMod 2) _]
            simp +decide)]
    -- By induction on $y$, we can show that $f(x, y) = f(x, 0)$ for all $x$ and $y$.
    have h_ind : ∀ x y, f (x, y) = f (x, ⟨0, by linarith [Fact.out (p := 0 < L)]⟩) := by
      intro x y; induction' y with y ih;
      induction' y with y ih;
      · rfl;
      · convert h_const x ⟨ y, by linarith ⟩ using 1;
        · congr;
          norm_num [ Fin.val_add, Nat.mod_eq_of_lt ih ];
        · exact Eq.symm ( by solve_by_elim [ Nat.lt_of_succ_lt ] );
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
    -- By induction on $x$, we can show that $f(x, 0) = f(0, 0)$ for all $x$.
    have h_ind_x :
        ∀ x, f (x, ⟨0, by linarith [Fact.out (p := 0 < L)]⟩) =
          f (⟨0, by linarith [Fact.out (p := 0 < L)]⟩,
            ⟨0, by linarith [Fact.out (p := 0 < L)]⟩) := by
      intro x
      induction' x with x ih;
      induction' x with x ih;
      · rfl;
      · convert h_const_x ⟨ x, by linarith ⟩ using 1;
        · exact Fin.ext ( by simp +decide [ next, Nat.mod_eq_of_lt ih ] );
        · exact Eq.symm ( by solve_by_elim [ Nat.lt_of_succ_lt ] );
    exact
      ⟨f (⟨0, by linarith [Fact.out (p := 0 < L)]⟩, ⟨0, by linarith [Fact.out (p := 0 < L)]⟩),
        funext fun x => by aesop⟩
  refine finrank_eq_one_iff'.mpr ?_
  refine ⟨⟨fun _ => 1, ?_⟩, ?_, ?_⟩ <;> norm_num
  · ext e; cases e <;> simp +decide [ toricBoundary2 ] ;
    · grind;
    · grind +qlia;
  · exact fun h => by simpa using congr_fun h ( ⟨ 0, Fact.out ⟩, ⟨ 0, Fact.out ⟩ ) ;
  · intro f hf; obtain ⟨ c, rfl ⟩ := h_span f hf; exact ⟨ c, by ext; simp +decide ⟩ ;

/-- Target boundary-space dimension formula. -/
theorem toric_finrank_boundaries :
    Module.finrank (ZMod 2) (toricBoundaries (L := L)) = L * L - 1 := by
  have hrn := toric_rank_nullity_boundary2 (L := L)
  have hC2 := toric_finrank_C2 (L := L)
  have hker := toric_finrank_ker_boundary2_eq_one (L := L)
  omega

/-- Quotient-dimension bridge for `H₁ = Z₁ / B₁`. -/
theorem toric_finrank_H1_eq_cycles_sub_boundaries
    :
    @Module.finrank (ZMod 2) (toricH1 (L := L)) _
      (Submodule.Quotient.addCommGroup (toricBoundarySubmoduleInCycles (L := L))).toAddCommMonoid
      (Submodule.Quotient.module (toricBoundarySubmoduleInCycles (L := L))) =
      Module.finrank (ZMod 2) (toricCycles (L := L)) -
        Module.finrank (ZMod 2) (toricBoundaries (L := L)) := by
  have hquot :
      @Module.finrank (ZMod 2) (toricH1 (L := L)) _
          (Submodule.Quotient.addCommGroup
            (toricBoundarySubmoduleInCycles (L := L))).toAddCommMonoid
          (Submodule.Quotient.module (toricBoundarySubmoduleInCycles (L := L))) +
          Module.finrank (ZMod 2) (toricBoundarySubmoduleInCycles (L := L)) =
        Module.finrank (ZMod 2) (toricCycles (L := L)) := by
    simpa [toricH1, toricBoundarySubmoduleInCycles] using
      (Submodule.finrank_quotient_add_finrank (R := ZMod 2)
        (toricBoundarySubmoduleInCycles (L := L)))
  have hcomap :
      Module.finrank (ZMod 2) (toricBoundarySubmoduleInCycles (L := L)) =
        Module.finrank (ZMod 2) (toricBoundaries (L := L)) := by
    simpa [toricBoundarySubmoduleInCycles] using
      (Submodule.comapSubtypeEquivOfLe (toric_boundaries_le_cycles (L := L))).finrank_eq
  rw [hcomap] at hquot
  exact Nat.eq_sub_of_add_eq hquot

/-- `dim(H₁) = 2` for the toric chain complex over `ZMod 2`. -/
theorem toric_finrank_H1_eq_two
    :
    @Module.finrank (ZMod 2) (toricH1 (L := L)) _
      (Submodule.Quotient.addCommGroup (toricBoundarySubmoduleInCycles (L := L))).toAddCommMonoid
      (Submodule.Quotient.module (toricBoundarySubmoduleInCycles (L := L))) = 2 := by
  have hH := toric_finrank_H1_eq_cycles_sub_boundaries (L := L)
  have hC := toric_finrank_cycles (L := L)
  have hB := toric_finrank_boundaries (L := L)
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
