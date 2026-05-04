import QEC.Stabilizer.Lattice.ToricLogicalCorrespondenceZ
import QEC.Stabilizer.Lattice.ToricWrappingInvariants
import Mathlib.LinearAlgebra.Matrix.Rank

namespace Quantum
namespace Stabilizer
namespace Lattice

open scoped BigOperators

/-!
# Dual wrapping invariants for the toric code (Z-type)

Mirror of `ToricWrappingInvariants` for the dual chain complex.

Dual invariants on `toricDualCycles`:
  `hRowAt y₀ c = ∑ x, c (H x y₀)`  — row parity of H-edges; independent of y₀ on dual cycles.
  `vColAt x₀ c = ∑ y, c (V x₀ y)`  — column parity of V-edges; independent of x₀ on dual cycles.

Both invariants vanish on `toricDualBoundaries`, inducing an isomorphism
  H¹_dual ≅ (ZMod 2)²
via `(hRowAt, vColAt)`.
-/

variable (L : ℕ)

-- ---------------------------------------------------------------------------
-- 1.  Dual wrapping invariants
-- ---------------------------------------------------------------------------

/-- Row parity of H-edges at fixed row `y₀`. -/
def hRowAt (y0 : Fin L) (c : C1 L) : ZMod 2 :=
  ∑ x : Fin L, c (EdgeIdx.h x y0)

/-- Column parity of V-edges at fixed column `x₀`. -/
def vColAt (x0 : Fin L) (c : C1 L) : ZMod 2 :=
  ∑ y : Fin L, c (EdgeIdx.v x0 y)

/-- Linear-map packaging of `hRowAt`. -/
def hRowAtLinear (y0 : Fin L) : C1 L →ₗ[ZMod 2] ZMod 2 where
  toFun := hRowAt (L := L) y0
  map_add' := by intro c d; simp [hRowAt, Finset.sum_add_distrib]
  map_smul' := by intro a c; simp [hRowAt, Finset.mul_sum]

/-- Linear-map packaging of `vColAt`. -/
def vColAtLinear (x0 : Fin L) : C1 L →ₗ[ZMod 2] ZMod 2 where
  toFun := vColAt (L := L) x0
  map_add' := by intro c d; simp [vColAt, Finset.sum_add_distrib]
  map_smul' := by intro a c; simp [vColAt, Finset.mul_sum]

variable [Fact (0 < L)]

-- ---------------------------------------------------------------------------
-- 2.  Independence on dual cycles
-- ---------------------------------------------------------------------------

/-- `hRowAt` is linear in the chain. -/
theorem hRowAt_linear (y0 : Fin L) :
    ∀ c d : C1 L, hRowAt (L := L) y0 (c + d) = hRowAt (L := L) y0 c + hRowAt (L := L) y0 d := by
  intro c d; simp [hRowAt, Finset.sum_add_distrib]

/-- `vColAt` is linear in the chain. -/
theorem vColAt_linear (x0 : Fin L) :
    ∀ c d : C1 L, vColAt (L := L) x0 (c + d) = vColAt (L := L) x0 c + vColAt (L := L) x0 d := by
  intro c d; simp [vColAt, Finset.sum_add_distrib]

/-
`hRowAt` is independent of the chosen row on dual cycles.
-/
theorem hRowAt_independent_on_dualCycles (c : toricDualCycles (L := L)) (y0 y1 : Fin L) :
    hRowAt (L := L) y0 c.1 = hRowAt (L := L) y1 c.1 := by
  -- By definition of `toricDualCycles`, we know that `toricDualBoundary L c = 0`.
  have h_dual_boundary_zero : toricDualBoundary L c.1 = 0 := by
    exact c.2;
  have h_row_eq : ∀ y : Fin L, hRowAt L y c.1 + hRowAt L (next L y) c.1 = 0 := by
    intro y
    have h_sum_zero : ∑ x : Fin L, (c.val (EdgeIdx.h x y) + c.val (EdgeIdx.h x (next L y)) + c.val (EdgeIdx.v x y) + c.val (EdgeIdx.v (next L x) y)) = 0 := by
      convert congr_arg ( fun f : FaceIdx L → ZMod 2 => ∑ x : Fin L, f ( x, y ) ) h_dual_boundary_zero using 1;
      norm_num;
    have h_sum_zero : ∑ x : Fin L, c.val (EdgeIdx.v x y) = ∑ x : Fin L, c.val (EdgeIdx.v (next L x) y) := by
      rcases L with ( _ | _ | L ) <;> norm_num at *;
      · fin_cases y ; rfl;
      · rw [ ← Equiv.sum_comp ( Equiv.addRight 1 ) ] ; norm_num [ Fin.add_def, next ];
    simp_all +decide [ Finset.sum_add_distrib, hRowAt ];
    grind;
  -- By induction on $k$, we can show that $hRowAt L y c = hRowAt L (y + k) c$ for any $k$.
  have h_induction : ∀ k : ℕ, ∀ y : Fin L, hRowAt L y c.1 = hRowAt L (Fin.mk ((y.val + k) % L) (Nat.mod_lt _ (Fact.out))) c.1 := by
    intro k y; induction' k with k ih <;> simp_all +decide [ ← add_assoc, Nat.mod_eq_of_lt ] ;
    specialize h_row_eq ⟨ ( y + k ) % L, Nat.mod_lt _ ( Fact.out ) ⟩ ; simp_all +decide [ ← eq_sub_iff_add_eq', next ] ;
  convert h_induction ( y1.val + L - y0.val ) y0 using 1;
  simp +decide [ add_tsub_cancel_of_le ( show ( y0 : ℕ ) ≤ y1 + L from by linarith [ Fin.is_lt y0, Fin.is_lt y1 ] ), Nat.mod_eq_of_lt ]

/-
`vColAt` is independent of the chosen column on dual cycles.
-/
theorem vColAt_independent_on_dualCycles (c : toricDualCycles (L := L)) (x0 x1 : Fin L) :
    vColAt (L := L) x0 c.1 = vColAt (L := L) x1 c.1 := by
  have hvColAt_linear : ∀ x : Fin L, vColAt (L := L) x c.1 + vColAt (L := L) (next L x) c.1 = 0 := by
    intro x
    have h_sum : ∑ y : Fin L, (c.val (EdgeIdx.h x y) + c.val (EdgeIdx.h x (next L y)) + c.val (EdgeIdx.v x y) + c.val (EdgeIdx.v (next L x) y)) = 0 := by
      have h_sum : ∀ y : Fin L, c.val (EdgeIdx.h x y) + c.val (EdgeIdx.h x (next L y)) + c.val (EdgeIdx.v x y) + c.val (EdgeIdx.v (next L x) y) = 0 := by
        intro y
        have := c.2
        simp [toricDualCycles] at this;
        convert congr_arg ( fun f : C2 L => f ( x, y ) ) c.2 using 1;
      exact Finset.sum_eq_zero fun y _ => h_sum y;
    simp_all +decide [ Finset.sum_add_distrib, vColAt ];
    have h_sum_h : ∑ y : Fin L, c.val (EdgeIdx.h x y) = ∑ y : Fin L, c.val (EdgeIdx.h x (next L y)) := by
      rcases L with ( _ | _ | L ) <;> simp_all +decide [ Finset.sum_add_distrib, Finset.mul_sum _ _ _, Finset.sum_mul _ _ _, next ];
      rw [ ← Equiv.sum_comp ( Equiv.addRight 1 ) ] ; norm_num [ Fin.add_def, Nat.mod_eq_of_lt ];
    grind;
  -- By induction on $k$, we can show that $vColAt x = vColAt (x + k)$ for any $k$.
  have hvColAt_induction : ∀ k : ℕ, ∀ x : Fin L, vColAt (L := L) x c.1 = vColAt (L := L) (Nat.rec x (fun _ x => next L x) k) c.1 := by
    intro k x; induction k <;> simp_all +decide [ ← eq_sub_iff_add_eq' ] ;
  -- By induction on $k$, we can show that $vColAt x = vColAt (x + k)$ for any $k$. Hence, $vColAt x0 = vColAt x1$.
  have hvColAt_eq : ∃ k : ℕ, Nat.rec x0 (fun _ x => next L x) k = x1 := by
    use (x1.val + L - x0.val) % L;
    have hvColAt_eq : ∀ k : ℕ, Nat.rec x0 (fun _ x => next L x) k = Fin.mk ((x0.val + k) % L) (Nat.mod_lt _ (Fact.out : 0 < L)) := by
      intro k; induction k <;> simp_all +decide [ Nat.mod_eq_of_lt, Fin.ext_iff, next ] ;
      ring;
    simp +decide [ hvColAt_eq, Nat.add_sub_of_le ( show ( x0 : ℕ ) ≤ x1 + L from by linarith [ Fin.is_lt x0, Fin.is_lt x1 ] ) ];
    exact Fin.ext ( Nat.mod_eq_of_lt x1.2 );
  exact hvColAt_eq.elim fun k hk => hvColAt_induction k x0 ▸ hk ▸ rfl

/-
---------------------------------------------------------------------------
3.  Boundary triviality
---------------------------------------------------------------------------

Dual boundaries have trivial `hRowAt` invariant.
-/
theorem hRowAt_dualBoundary_zero (b : toricDualBoundaries (L := L)) :
    hRowAt (L := L) (zeroCoord L) b.1 = 0 := by
  rcases b with ⟨ b, ⟨ s, rfl ⟩ ⟩;
  unfold hRowAt toricVertexCutMap;
  simp +decide [ Finset.sum_add_distrib, next ];
  rcases L with ( _ | _ | L ) <;> norm_num at *;
  · erw [ Finset.sum_singleton ] ; ring_nf!;
    grobner;
  · erw [ ← Equiv.sum_comp ( Equiv.addRight 1 ) ] ; norm_num [ Fin.add_def, Nat.mod_eq_of_lt ];
    grind

/-
Dual boundaries have trivial `vColAt` invariant.
-/
theorem vColAt_dualBoundary_zero (b : toricDualBoundaries (L := L)) :
    vColAt (L := L) (zeroCoord L) b.1 = 0 := by
  rcases b with ⟨ b, hb ⟩;
  obtain ⟨ s, rfl ⟩ := hb;
  unfold vColAt toricVertexCutMap; simp +decide [ Finset.sum_add_distrib ] ;
  rcases L with ( _ | _ | L ) <;> simp_all +decide [ ZMod ];
  · have h2 : (2 : ZMod 2) = 0 := by decide
    calc
      s (zeroCoord 1, 0) + s (zeroCoord 1, next 1 0)
          = s (zeroCoord 1, 0) + s (zeroCoord 1, 0) := by simp [next]
      _ = (2 : ZMod 2) * s (zeroCoord 1, 0) := by simp [two_mul]
      _ = 0 := by simp [h2]
  · rw [ ← Equiv.sum_comp ( Equiv.addRight 1 ) ] ; simp +decide [ Fin.add_def, Nat.mod_eq_of_lt ];
    simp [ next ];
    have h : ∀ (a : ZMod 2), a + a = 0 := by decide
    exact h _

-- ---------------------------------------------------------------------------
-- 4.  The quotient map φ_Z : H¹_dual → (ZMod 2)²
-- ---------------------------------------------------------------------------

/-- Dual homology quotient: toricDualCycles / toricDualBoundaries (as submodule in cycles). -/
noncomputable abbrev toricDualBoundarySubmoduleInCycles : Submodule (ZMod 2) (toricDualCycles (L := L)) :=
  Submodule.comap (toricDualCycles (L := L)).subtype (toricDualBoundaries (L := L))

/-- The dual H¹ quotient type. -/
abbrev toricDualH1 : Type :=
  toricDualCycles (L := L) ⧸ toricDualBoundarySubmoduleInCycles (L := L)

/-- Quotient-level map `(hRowAt, vColAt)` on dual cycles, well-defined modulo dual boundaries. -/
noncomputable def phiDual : toricDualH1 (L := L) → ZMod 2 × ZMod 2 :=
  let N : Submodule (ZMod 2) (toricDualCycles (L := L)) :=
    Submodule.comap (toricDualCycles (L := L)).subtype (toricDualBoundaries (L := L))
  let phiDualLin : toricDualCycles (L := L) →ₗ[ZMod 2] ZMod 2 × ZMod 2 :=
    { toFun := fun c => (hRowAt (L := L) (zeroCoord L) c.1, vColAt (L := L) (zeroCoord L) c.1)
      map_add' := fun a b => by
        simp only [Submodule.coe_add]
        exact Prod.ext (hRowAt_linear (L := L) (zeroCoord L) a.1 b.1)
                       (vColAt_linear (L := L) (zeroCoord L) a.1 b.1)
      map_smul' := fun r c => by
        simp only [RingHom.id_apply, Submodule.coe_smul_of_tower]
        ext <;> simp [hRowAt, vColAt, Finset.mul_sum] }
  Submodule.liftQ N phiDualLin (by
    intro c hc
    rw [LinearMap.mem_ker]
    rw [Submodule.mem_comap] at hc
    have hh := hRowAt_dualBoundary_zero (L := L) ⟨c.1, hc⟩
    have hv := vColAt_dualBoundary_zero (L := L) ⟨c.1, hc⟩
    exact Prod.ext hh hv)

/-- `phiDual` agrees with the underlying linear lift on equivalence classes. -/
theorem phiDual_liftQ_eq (c : toricDualCycles (L := L)) :
    phiDual (L := L) (Submodule.Quotient.mk c) =
      (hRowAt (L := L) (zeroCoord L) c.1, vColAt (L := L) (zeroCoord L) c.1) := by
  simp only [phiDual, Submodule.liftQ_apply, LinearMap.coe_mk, AddHom.coe_mk]

/-
---------------------------------------------------------------------------
5.  Surjectivity and injectivity
---------------------------------------------------------------------------

`phiDual` is surjective.
-/
theorem phiDual_surjective :
    Function.Surjective (phiDual (L := L)) := by
  intro p
  obtain ⟨a, b⟩ := p
  generalize_proofs at *;
  obtain ⟨c, hc⟩ : ∃ c : toricDualCycles (L := L), hRowAt (L := L) (zeroCoord L) c.1 = a ∧ vColAt (L := L) (zeroCoord L) c.1 = b := by
    -- Define the chain $c$ such that it has $a$ horizontal edges and $b$ vertical edges.
    obtain ⟨c, hc⟩ : ∃ c : C1 L, (∑ x : Fin L, c (EdgeIdx.h x (zeroCoord L))) = a ∧ (∑ y : Fin L, c (EdgeIdx.v (zeroCoord L) y)) = b := by
      refine' ⟨ fun e => if e = EdgeIdx.h ( zeroCoord L ) ( zeroCoord L ) then a else if e = EdgeIdx.v ( zeroCoord L ) ( zeroCoord L ) then b else 0, _, _ ⟩ <;> simp +decide [ Finset.sum_ite, Finset.filter_eq', Finset.filter_ne' ]
    generalize_proofs at *; (
    -- Define the chain $c'$ such that it has $a$ horizontal edges and $b$ vertical edges.
    obtain ⟨c', hc'⟩ : ∃ c' : C1 L, (∀ x y, c' (EdgeIdx.h x y) = c (EdgeIdx.h x (zeroCoord L))) ∧ (∀ x y, c' (EdgeIdx.v x y) = c (EdgeIdx.v (zeroCoord L) y)) ∧ (∀ p : FaceIdx L, toricDualBoundary L c' p = 0) := by
      refine' ⟨ fun e => match e with | EdgeIdx.h x y => c ( EdgeIdx.h x ( zeroCoord L ) ) | EdgeIdx.v x y => c ( EdgeIdx.v ( zeroCoord L ) y ), _, _, _ ⟩ <;> simp +decide [ toricDualBoundary ];
      grind +ring
    generalize_proofs at *; (
    use ⟨c', by
      exact LinearMap.mem_ker.mpr ( by ext p; exact hc'.2.2 p )⟩
    generalize_proofs at *; (
    unfold hRowAt vColAt; aesop;)))
  generalize_proofs at *; exact ⟨Submodule.Quotient.mk c, by
    rw [ phiDual_liftQ_eq ] ; aesop;⟩;

/-
Dimension of the dual cycle space.
-/
theorem toric_finrank_dualCycles :
    Module.finrank (ZMod 2) (toricDualCycles (L := L)) = L * L + 1 := by
  have := LinearMap.finrank_range_add_finrank_ker ( toricDualBoundary L ) ; simp_all +decide [ toric_finrank_C1 ] ;
  have h_dual_boundary_range : Module.finrank (ZMod 2) (LinearMap.range (toricDualBoundary L)) = Module.finrank (ZMod 2) (LinearMap.range (toricBoundary2 (L := L))) := by
    have h_dual_boundary : LinearMap.rank (toricDualBoundary L) = LinearMap.rank (toricBoundary2 (L := L)) := by
      have h_dual_boundary : (toricDualBoundary L).toMatrix' = (toricBoundary2 (L := L)).toMatrix'.transpose := by
        ext ⟨x, y⟩ e; simp [LinearMap.toMatrix', toricDualBoundary, toricBoundary2];
        cases e <;> simp +decide [ Pi.single_apply ];
        · grind;
        · grind +splitImp
      have h_dual_boundary : Matrix.rank (toricDualBoundary L).toMatrix' = Matrix.rank (toricBoundary2 (L := L)).toMatrix' := by
        rw [ h_dual_boundary, Matrix.rank_transpose ];
      convert h_dual_boundary using 1;
      simp +decide [ Matrix.rank, LinearMap.rank ];
      simp +decide [ ← Module.finrank_eq_rank ];
      convert Iff.rfl;
      all_goals ext; simp +decide [ LinearMap.toMatrix' ];
    simp +decide [ Module.finrank, Cardinal.mk_fintype ];
    grind +splitImp;
  have := toric_finrank_boundaries ( L := L ) ; simp_all +decide [ mul_assoc ] ;
  linarith! [ Nat.sub_add_cancel ( show 1 ≤ L * L from Nat.mul_pos ( Fact.out ) ( Fact.out ) ) ]

/-
Dimension of the dual boundary space.
-/
theorem toric_finrank_dualBoundaries :
    Module.finrank (ZMod 2) (toricDualBoundaries (L := L)) = L * L - 1 := by
  -- By definition of `toricDualBoundaries`, we know that it is the range of the vertex cut map.
  have h_dualBoundaries_range : toricDualBoundaries L = LinearMap.range (toricVertexCutMap (L := L)) := by
    exact rfl;
  rw [ h_dualBoundaries_range ];
  have := LinearMap.finrank_range_add_finrank_ker ( toricVertexCutMap ( L := L ) );
  rw [ show Module.finrank ( ZMod 2 ) ( C0 L ) = L * L from ?_ ] at this;
  · refine' eq_tsub_of_add_eq _;
    convert this;
    exact?;
  · simp +decide [ C0, Module.finrank ]

/-- `phiDual` as an explicit linear map (for injectivity via dimension count). -/
noncomputable def phiDualLinearMap :
    (toricDualCycles (L := L) ⧸
      Submodule.comap (toricDualCycles (L := L)).subtype (toricDualBoundaries (L := L))) →ₗ[ZMod 2]
    ZMod 2 × ZMod 2 :=
  Submodule.liftQ _ {
    toFun := fun c => (hRowAt (L := L) (zeroCoord L) c.1, vColAt (L := L) (zeroCoord L) c.1)
    map_add' := fun a b => by
      simp only [Submodule.coe_add]
      exact Prod.ext (hRowAt_linear (L := L) (zeroCoord L) a.1 b.1)
                     (vColAt_linear (L := L) (zeroCoord L) a.1 b.1)
    map_smul' := fun r c => by
      simp only [RingHom.id_apply, Submodule.coe_smul_of_tower]
      ext <;> simp [hRowAt, vColAt, Finset.mul_sum]
  } (by
    intro c hc
    simp only [LinearMap.mem_ker]
    have hc' : c.1 ∈ toricDualBoundaries (L := L) := by
      rwa [Submodule.mem_comap] at hc
    have hh := hRowAt_dualBoundary_zero (L := L) ⟨c.1, hc'⟩
    have hv := vColAt_dualBoundary_zero (L := L) ⟨c.1, hc'⟩
    exact Prod.ext hh hv)

/-- `phiDual` agrees with `phiDualLinearMap`. -/
theorem phiDual_eq_phiDualLinearMap (x : toricDualH1 (L := L)) :
    phiDual (L := L) x = phiDualLinearMap (L := L) x := by
  convert rfl

/-
`phiDual` is injective.
-/
theorem phiDual_injective :
    Function.Injective (phiDual (L := L)) := by
  have h_finrank : Module.finrank (ZMod 2) (toricDualH1 (L := L)) = 2 := by
    have h_finrank : Module.finrank (ZMod 2) (toricDualCycles (L := L)) - Module.finrank (ZMod 2) (toricDualBoundaries (L := L)) = 2 := by
      rw [ toric_finrank_dualCycles, toric_finrank_dualBoundaries ];
      exact Nat.sub_eq_of_eq_add <| by linarith [ Nat.sub_add_cancel <| show 1 ≤ L * L from Nat.mul_pos ( Fact.out ) ( Fact.out ) ] ;
    have := Submodule.finrank_quotient_add_finrank ( Submodule.comap ( toricDualCycles ( L := L ) ).subtype ( toricDualBoundaries ( L := L ) ) );
    rw [ Nat.sub_eq_iff_eq_add ] at h_finrank;
    · rw [ ← LinearEquiv.finrank_eq ( Submodule.comapSubtypeEquivOfLe ( show toricDualBoundaries ( L := L ) ≤ toricDualCycles ( L := L ) from by exact? ) ) ] at * ; linarith!;
    · exact le_of_lt ( Nat.lt_of_sub_eq_succ h_finrank );
  have := @phiDual_surjective L ‹_›;
  have h_finrank : Module.finrank (ZMod 2) (↥(LinearMap.range (phiDualLinearMap (L := L)))) = 2 := by
    rw [ LinearMap.range_eq_top.mpr ] <;> norm_num [ this ];
    convert this using 1;
  have := LinearMap.finrank_range_add_finrank_ker ( phiDualLinearMap ( L := L ) ) ; simp_all +decide ;
  convert LinearMap.ker_eq_bot.mp this using 1

/-
`H¹_dual ≅ (ZMod 2)²` via dual wrapping invariants.
-/
theorem phiDual_equiv :
    ∃ _ : toricDualH1 (L := L) ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2), True := by
  use (LinearEquiv.ofBijective (phiDualLinearMap (L := L)) ⟨phiDual_injective (L := L), phiDual_surjective (L := L)⟩)

end Lattice
end Stabilizer
end Quantum
