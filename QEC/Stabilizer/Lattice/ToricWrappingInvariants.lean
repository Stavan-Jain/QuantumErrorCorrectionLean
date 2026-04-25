import Mathlib.Tactic
import QEC.Stabilizer.Lattice.ToricHomology

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
  sorry

/-- `vAt` is independent of the chosen row on cycles. -/
theorem vAt_independent_on_cycles (c : toricCycles (L := L)) (y0 y1 : Fin L) :
    vAt (L := L) y0 c.1 = vAt (L := L) y1 c.1 := by
  sorry

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
  sorry

/-- Injectivity scaffold for `φ`. -/
theorem phi_injective :
    Function.Injective (phi (L := L)) := by
  sorry

/-- `H₁ ≃ (Z/2Z)²` via wrapping invariants. -/
theorem phi_equiv
    [AddCommMonoid (toricH1 (L := L))]
    [Module (ZMod 2) (toricH1 (L := L))] :
    ∃ e : toricH1 (L := L) ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2), True := by
  sorry

end Lattice
end Stabilizer
end Quantum
