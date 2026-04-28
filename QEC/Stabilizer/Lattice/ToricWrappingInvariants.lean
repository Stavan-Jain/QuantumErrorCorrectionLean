import Mathlib.Tactic
import QEC.Stabilizer.Lattice.ToricHomology
import QEC.Stabilizer.Lattice.ToricH1Dimension


namespace Quantum
namespace Stabilizer
namespace Lattice

open scoped BigOperators

variable (L : ℕ)

/-- Distinguished coordinate `0 : Fin L` when `L > 0`. -/
def zeroCoord [Fact (0 < L)] : Fin L := ⟨0, Fact.out⟩

/-- Horizontal wrapping parity at fixed column `x₀`. -/
def hAt (x0 : Fin L) (c : C1 L) : ZMod 2 :=
  ∑ y : Fin L, c (EdgeIdx.h x0 y)

/-- Vertical wrapping parity at fixed row `y₀`. -/
def vAt (y0 : Fin L) (c : C1 L) : ZMod 2 :=
  ∑ x : Fin L, c (EdgeIdx.v x y0)

/-- Linear-map packaging of `hAt`. -/
def hAtLinear (x0 : Fin L) : C1 L →ₗ[ZMod 2] ZMod 2 where
  toFun := hAt (L := L) x0
  map_add' := by
    intro c d
    simp [hAt, Finset.sum_add_distrib]
  map_smul' := by
    intro a c
    simp [hAt, Finset.mul_sum]

/-- Linear-map packaging of `vAt`. -/
def vAtLinear (y0 : Fin L) : C1 L →ₗ[ZMod 2] ZMod 2 where
  toFun := vAt (L := L) y0
  map_add' := by
    intro c d
    simp [vAt, Finset.sum_add_distrib]
  map_smul' := by
    intro a c
    simp [vAt, Finset.mul_sum]

variable [Fact (0 < L)]

/-- Section-6 invariant `h` on cycles (using distinguished column `x=0`). -/
def hWrap (c : toricCycles (L := L)) : ZMod 2 :=
  hAt (L := L) (zeroCoord L) c.1

/-- Section-6 invariant `v` on cycles (using distinguished row `y=0`). -/
def vWrap (c : toricCycles (L := L)) : ZMod 2 :=
  vAt (L := L) (zeroCoord L) c.1

/-- Pairing of cycle invariants `(h,v)` before quotienting by boundaries. -/
def phiOnCycles (c : toricCycles (L := L)) : ZMod 2 × ZMod 2 :=
  (hWrap (L := L) c, vWrap (L := L) c)

/-- `hAt` is linear in the chain argument. -/
theorem hAt_linear (x0 : Fin L) :
    ∀ c d : C1 L, hAt (L := L) x0 (c + d) = hAt (L := L) x0 c + hAt (L := L) x0 d := by
  let _ := (Fact.out : 0 < L)
  intro c d
  simp [hAt, Finset.sum_add_distrib]

/-- `vAt` is linear in the chain argument. -/
theorem vAt_linear (y0 : Fin L) :
    ∀ c d : C1 L, vAt (L := L) y0 (c + d) = vAt (L := L) y0 c + vAt (L := L) y0 d := by
  let _ := (Fact.out : 0 < L)
  intro c d
  simp [vAt, Finset.sum_add_distrib]

/-- `hAt` is independent of the chosen column on cycles. -/
theorem hAt_independent_on_cycles (c : toricCycles (L := L)) (x0 x1 : Fin L) :
    hAt (L := L) x0 c.1 = hAt (L := L) x1 c.1 := by
  have hAt_indep : ∀ x : Fin L, hAt L x c.1 = hAt L (prev L x) c.1 := by
    intro x
    have h_sum_zero :
        ∑ y : Fin L,
          (c.val (EdgeIdx.h x y) + c.val (EdgeIdx.h (prev L x) y) +
            c.val (EdgeIdx.v x y) + c.val (EdgeIdx.v x (prev L y))) = 0 := by
      have h_diff : ∀ y : Fin L,
          c.val (EdgeIdx.h x y) + c.val (EdgeIdx.h (prev L x) y) +
            c.val (EdgeIdx.v x y) + c.val (EdgeIdx.v x (prev L y)) = 0 := by
        intro y
        have h_cycle : toricBoundary1 (L := L) c.val (x, y) = 0 := by
          exact c.2 |> fun h => by simp ;
        convert h_cycle using 1;
      aesop;
    simp_all +decide [ Finset.sum_add_distrib, hAt ];
    have h_sum_zero :
        ∑ y : Fin L, c.val (EdgeIdx.v x (prev L y)) =
          ∑ y : Fin L, c.val (EdgeIdx.v x y) := by
      apply Finset.sum_bij (fun y _ => prev L y);
      · simp;
      · exact fun a₁ _ a₂ _ h => by simpa using congr_arg ( fun x => next L x ) h;
      · exact fun y _ => ⟨ next L y, Finset.mem_univ _, by simp +decide ⟩;
      · exact fun _ _ => rfl;
    grind;
  -- Induct on the modular offset from `x0` to `x1`.
  have h_ind :
      ∀ k : ℕ,
        hAt L (Fin.mk ((x0.val + k) % L) (Nat.mod_lt _ Fact.out)) c.1 = hAt L x0 c.1 := by
    intro k;
    induction k with
    | zero =>
        norm_num [Nat.mod_eq_of_lt]
    | succ k ih =>
        convert ih using 1
        convert hAt_indep _ using 2
        unfold prev
        norm_num [add_assoc, Nat.mod_eq_of_lt]
        rw [show 1 + (L - 1) = L by
          rw [add_tsub_cancel_of_le (by linarith [Fin.is_lt x0, Fact.out (p := 0 < L)])]]
        norm_num [Nat.add_mod]
  convert h_ind ( x1.val + L - x0.val ) |> Eq.symm using 2;
  norm_num [add_tsub_cancel_of_le
    (show (x0 : ℕ) ≤ x1 + L from by linarith [Fin.is_lt x0, Fin.is_lt x1]), Nat.mod_eq_of_lt]

/-- `vAt` is independent of the chosen row on cycles. -/
theorem vAt_independent_on_cycles (c : toricCycles (L := L)) (y0 y1 : Fin L) :
    vAt (L := L) y0 c.1 = vAt (L := L) y1 c.1 := by
  have h_B1_gen : ∀ y : Fin L, vAt (L := L) y (c.1) = vAt (L := L) (prev (L := L) y) (c.1) := by
    intro y
    have h_sum_eq :
        ∑ x : Fin L,
          (c.val (EdgeIdx.h x y) + c.val (EdgeIdx.h (prev (L := L) x) y) +
            c.val (EdgeIdx.v x y) + c.val (EdgeIdx.v x (prev (L := L) y))) = 0 := by
      have h_sum_eq : ∀ x : Fin L,
          c.val (EdgeIdx.h x y) + c.val (EdgeIdx.h (prev (L := L) x) y) +
            c.val (EdgeIdx.v x y) + c.val (EdgeIdx.v x (prev (L := L) y)) = 0 := by
        intro x; have := c.2; simp_all +decide [ toricCycles ] ;
        convert congr_arg ( fun f => f ( x, y ) ) c.2 using 1;
      aesop;
    simp_all +decide [ Finset.sum_add_distrib, vAt ];
    rw [show ∑ x : Fin L, (c : EdgeIdx L → ZMod 2) (EdgeIdx.h (prev L x) y) =
        ∑ x : Fin L, (c : EdgeIdx L → ZMod 2) (EdgeIdx.h x y) from ?_] at h_sum_eq
    · grind +splitImp;
    · apply Finset.sum_bij (fun x _ => prev (L := L) x);
      · simp;
      · exact fun x _ y _ h => by simpa using congr_arg ( fun z => next L z ) h;
      · exact fun x _ => ⟨ next L x, Finset.mem_univ _, by simp +decide ⟩;
      · exact fun _ _ => rfl;
  -- Induct on the modular offset from `y0` to `y1`.
  have h_ind : ∀ k : ℕ, ∀ y : Fin L,
      vAt (L := L) y (c.1) =
        vAt (L := L) (Fin.mk ((y.val + k) % L) (Nat.mod_lt _ (Fact.out : 0 < L))) (c.1) := by
    intro k y
    induction' k with k ih <;> simp +decide [Nat.add_mod, Nat.mod_eq_of_lt]
    simp +decide [ih]
    convert h_B1_gen _ |> Eq.symm using 2
    norm_num [add_assoc, Nat.mod_eq_of_lt]
    norm_num [← add_assoc, next]
  convert h_ind ( y1.val + L - y0.val ) y0 using 1;
  simp +decide [add_tsub_cancel_of_le
    (show (y0 : ℕ) ≤ y1 + L from by linarith [Fin.is_lt y0, Fin.is_lt y1]), Nat.mod_eq_of_lt]

/-- Boundaries have trivial `h` invariant. -/
theorem h_boundary_zero (b : toricBoundaries (L := L)) :
    hAt (L := L) (zeroCoord L) b.1 = 0 := by
  rcases b with ⟨b, hb⟩
  rcases hb with ⟨f, rfl⟩
  let z0 : Fin L := zeroCoord L
  have hprev_bij : Function.Bijective (prev L) := by
    refine ⟨?_, ?_⟩
    · intro y₁ y₂ h
      exact by simpa using congrArg (next L) h
    · intro y
      exact ⟨next L y, by simp⟩
  have hsum_prev :
      (∑ y : Fin L, f (z0, prev L y)) = ∑ y : Fin L, f (z0, y) := by
    simpa using (hprev_bij.sum_comp (g := fun y : Fin L => f (z0, y)))
  have hdouble_zero :
      (∑ y : Fin L, f (z0, y)) + (∑ y : Fin L, f (z0, y)) = 0 := by
    have h2 : (2 : ZMod 2) = 0 := by decide
    calc
      (∑ y : Fin L, f (z0, y)) + (∑ y : Fin L, f (z0, y))
          = (2 : ZMod 2) * (∑ y : Fin L, f (z0, y)) := by
            symm
            simp [two_mul]
      _ = 0 := by simp [h2]
  change (∑ y : Fin L,
      toricBoundary2 (L := L) f (EdgeIdx.h z0 y)) = 0
  simpa [toricBoundary2, Finset.sum_add_distrib, hsum_prev] using hdouble_zero

/-- Boundaries have trivial `v` invariant. -/
theorem v_boundary_zero (b : toricBoundaries (L := L)) :
    vAt (L := L) (zeroCoord L) b.1 = 0 := by
  rcases b with ⟨b, hb⟩
  rcases hb with ⟨f, rfl⟩
  let z0 : Fin L := zeroCoord L
  have hprev_bij : Function.Bijective (prev L) := by
    refine ⟨?_, ?_⟩
    · intro x₁ x₂ h
      exact by simpa using congrArg (next L) h
    · intro x
      exact ⟨next L x, by simp⟩
  have hsum_prev :
      (∑ x : Fin L, f (prev L x, z0)) = ∑ x : Fin L, f (x, z0) := by
    simpa using (hprev_bij.sum_comp (g := fun x : Fin L => f (x, z0)))
  have hdouble_zero :
      (∑ x : Fin L, f (x, z0)) + (∑ x : Fin L, f (x, z0)) = 0 := by
    have h2 : (2 : ZMod 2) = 0 := by decide
    calc
      (∑ x : Fin L, f (x, z0)) + (∑ x : Fin L, f (x, z0))
          = (2 : ZMod 2) * (∑ x : Fin L, f (x, z0)) := by
            symm
            simp [two_mul]
      _ = 0 := by simp [h2]
  change (∑ x : Fin L,
      toricBoundary2 (L := L) f (EdgeIdx.v x z0)) = 0
  simpa [toricBoundary2, Finset.sum_add_distrib, hsum_prev] using hdouble_zero

/-- Quotient-level `(h,v)` map is well-defined. -/
noncomputable def phi : toricH1 (L := L) → ZMod 2 × ZMod 2 :=
  -- Inline the boundary-submodule-in-cycles so Lean can synthesize instances on
  -- the explicit `⧸` quotient, sidestepping the opaque `toricH1` def.
  let N : Submodule (ZMod 2) (toricCycles (L := L)) :=
    Submodule.comap (toricCycles (L := L)).subtype (toricBoundaries (L := L))
  -- Define phiLin with an explicit toFun so application reduces by rfl,
  -- avoiding the `Pi.prod` intermediate form from `LinearMap.prod`.
  let phiLin : toricCycles (L := L) →ₗ[ZMod 2] ZMod 2 × ZMod 2 :=
    { toFun := fun c => (hAt (L := L) (zeroCoord L) c.1, vAt (L := L) (zeroCoord L) c.1)
      map_add' := fun a b => by
        simp only [Submodule.coe_add]
        exact Prod.ext (hAt_linear (L := L) (zeroCoord L) a.1 b.1)
                       (vAt_linear (L := L) (zeroCoord L) a.1 b.1)
      map_smul' := fun r c => by
        simp only [RingHom.id_apply, Submodule.coe_smul_of_tower]
        ext <;> simp [hAt, vAt, Finset.mul_sum] }
  -- `Submodule.liftQ` produces a linear map on `toricCycles L ⧸ N`,
  -- which is definitionally `toricH1 L`.
  Submodule.liftQ N phiLin (by
    intro c hc
    rw [LinearMap.mem_ker]
    rw [Submodule.mem_comap] at hc
    -- hc : c.1 ∈ toricBoundaries L
    have hh := h_boundary_zero (L := L) ⟨c.1, hc⟩
    have hv := v_boundary_zero (L := L) ⟨c.1, hc⟩
    exact Prod.ext hh hv)

/-- `phi` agrees with the underlying linear lift on equivalence classes. -/
theorem phi_liftQ_eq (c : toricCycles (L := L)) :
    phi (L := L) (Submodule.Quotient.mk c) =
      (hAt (L := L) (zeroCoord L) c.1, vAt (L := L) (zeroCoord L) c.1) := by
  simp only [phi, Submodule.liftQ_apply, LinearMap.coe_mk, AddHom.coe_mk]

/-- Surjectivity scaffold for `φ`. -/
theorem phi_surjective :
    Function.Surjective (phi (L := L)) := by
  unfold phi;
  intro x;
  rcases x with ⟨ x, y ⟩;
  -- Build a cycle with horizontal strip value `x` and vertical strip value `y`.
  obtain ⟨c, hc⟩ : ∃ c : C1 L,
      (∀ x' : Fin L, ∀ y' : Fin L, c (EdgeIdx.h x' y') = if y' = zeroCoord L then x else 0) ∧
      (∀ x' : Fin L, ∀ y' : Fin L, c (EdgeIdx.v x' y') = if x' = zeroCoord L then y else 0) ∧
      toricBoundary1 (L := L) c = 0 := by
    refine ⟨
      (fun e =>
        match e with
        | EdgeIdx.h x' y' => if y' = zeroCoord L then x else 0
        | EdgeIdx.v x' y' => if x' = zeroCoord L then y else 0),
      ?_, ?_, ?_⟩ <;>
      simp +decide [toricBoundary1]
    ext ⟨ x, y ⟩ ; ring;
    aesop;
  refine ⟨Submodule.Quotient.mk ⟨c, hc.2.2⟩, ?_⟩
  simp +decide [ hAt, vAt, hc ]

/-- phi as an explicit linear map. -/
noncomputable def phiLinearMap : (toricCycles (L := L) ⧸
    Submodule.comap (toricCycles (L := L)).subtype (toricBoundaries (L := L))) →ₗ[ZMod 2]
    ZMod 2 × ZMod 2 :=
  Submodule.liftQ _ {
    toFun := fun c => (hAt (L := L) (zeroCoord L) c.1, vAt (L := L) (zeroCoord L) c.1)
    map_add' := fun a b => by
      simp only [Submodule.coe_add]
      exact Prod.ext (hAt_linear (L := L) (zeroCoord L) a.1 b.1)
                     (vAt_linear (L := L) (zeroCoord L) a.1 b.1)
    map_smul' := fun r c => by
      simp only [RingHom.id_apply, Submodule.coe_smul_of_tower]
      ext <;> simp [hAt, vAt, Finset.mul_sum]
  } (by
    intro c hc
    rw [LinearMap.mem_ker]
    rw [Submodule.mem_comap] at hc
    have hh := h_boundary_zero (L := L) ⟨c.1, hc⟩
    have hv := v_boundary_zero (L := L) ⟨c.1, hc⟩
    exact Prod.ext hh hv)

/-
phi agrees with phiLinearMap.
-/
theorem phi_eq_phiLinearMap (x : toricH1 (L := L)) :
    phi (L := L) x = phiLinearMap (L := L) x := by
  convert rfl

/-- Injectivity scaffold for `φ`. -/
theorem phi_injective :
    Function.Injective (phi (L := L)) := by
  have h1 : Function.Injective (⇑(phiLinearMap (L := L))) ↔
      Function.Surjective (⇑(phiLinearMap (L := L))) := by
    apply LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    have : Module.finrank (ZMod 2)
        (↑(toricCycles (L := L)) ⧸
          Submodule.comap (toricCycles (L := L)).subtype (toricBoundaries (L := L))) = 2 :=
      toric_finrank_H1_eq_two (L := L)
    rw [this]
    simp [Module.finrank_prod]
  have h2 : Function.Surjective (⇑(phiLinearMap (L := L))) := by
    intro x
    obtain ⟨y, hy⟩ := phi_surjective (L := L) x
    exact ⟨y, by rw [← phi_eq_phiLinearMap]; exact hy⟩
  rw [show phi (L := L) = ⇑(phiLinearMap (L := L)) from
    funext (fun x => phi_eq_phiLinearMap L x)]
  exact h1.mpr h2

/-- `H₁ ≃ (Z/2Z)²` via wrapping invariants. -/
theorem phi_equiv
    :
    ∃ _ : toricH1 (L := L) ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2), True := by
  have hphiLin_inj : Function.Injective (⇑(phiLinearMap (L := L))) := by
    intro x y hxy
    apply phi_injective (L := L)
    simpa [phi_eq_phiLinearMap (L := L) x, phi_eq_phiLinearMap (L := L) y] using hxy
  have hphiLin_surj : Function.Surjective (⇑(phiLinearMap (L := L))) := by
    intro z
    obtain ⟨x, hx⟩ := phi_surjective (L := L) z
    refine ⟨x, ?_⟩
    simpa [phi_eq_phiLinearMap (L := L) x] using hx
  let e : toricH1 (L := L) ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2) :=
    LinearEquiv.ofBijective (phiLinearMap (L := L)) ⟨hphiLin_inj, hphiLin_surj⟩
  exact ⟨e, trivial⟩

end Lattice
end Stabilizer
end Quantum
