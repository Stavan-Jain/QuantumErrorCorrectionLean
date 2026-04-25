import Mathlib.Tactic
import QEC.Stabilizer.Lattice.ToricChains

namespace Quantum
namespace Stabilizer
namespace Lattice

open scoped BigOperators

variable (L : ℕ) [Fact (0 < L)]

/-- Boundary map `∂2 : C2 → C1` for the toric square cellulation over `ZMod 2`. -/
def toricBoundary2 : C2 L →ₗ[ZMod 2] C1 L where
  toFun f :=
    fun e => match e with
      | EdgeIdx.h x y => f (x, y) + f (x, prev L y)
      | EdgeIdx.v x y => f (x, y) + f (prev L x, y)
  map_add' := by
    intro f g
    ext e
    cases e <;> simp [add_assoc, add_comm, add_left_comm]
  map_smul' := by
    intro a f
    ext e
    cases e <;> simp [mul_add]

/-- Boundary map `∂1 : C1 → C0` for the toric square cellulation over `ZMod 2`. -/
def toricBoundary1 : C1 L →ₗ[ZMod 2] C0 L where
  toFun c :=
    fun v =>
      c (EdgeIdx.h v.1 v.2) + c (EdgeIdx.h (prev L v.1) v.2) +
      c (EdgeIdx.v v.1 v.2) + c (EdgeIdx.v v.1 (prev L v.2))
  map_add' := by
    intro c d
    ext v
    simp [add_assoc, add_comm, add_left_comm]
  map_smul' := by
    intro a c
    ext v
    simp [mul_add, add_assoc]

@[simp] lemma toricBoundary2_singleFace_apply_h (x y x' y' : Fin L) :
    toricBoundary2 (L := L) (singleFace (L := L) (x, y)) (EdgeIdx.h x' y') =
      (if (x', y') = (x, y) then (1 : ZMod 2) else 0) +
      (if (x', prev L y') = (x, y) then (1 : ZMod 2) else 0) := by
  simp [toricBoundary2, singleFace]

@[simp] lemma toricBoundary2_singleFace_apply_v (x y x' y' : Fin L) :
    toricBoundary2 (L := L) (singleFace (L := L) (x, y)) (EdgeIdx.v x' y') =
      (if (x', y') = (x, y) then (1 : ZMod 2) else 0) +
      (if (prev L x', y') = (x, y) then (1 : ZMod 2) else 0) := by
  simp [toricBoundary2, singleFace]

@[simp] lemma toricBoundary1_singleEdge_apply
    (e : EdgeIdx L) (v : VtxIdx L) :
    toricBoundary1 (L := L) (singleEdge (L := L) e) v =
      singleEdge (L := L) e (EdgeIdx.h v.1 v.2) +
      singleEdge (L := L) e (EdgeIdx.h (prev L v.1) v.2) +
      singleEdge (L := L) e (EdgeIdx.v v.1 v.2) +
      singleEdge (L := L) e (EdgeIdx.v v.1 (prev L v.2)) := by
  simp [toricBoundary1]

/-- Chain-complex law for toric boundaries. -/
theorem toricBoundary_comp_zero :
    (toricBoundary1 (L := L)).comp (toricBoundary2 (L := L)) = 0 := by
  sorry

/-- Pointwise corollary of `toricBoundary_comp_zero`. -/
theorem toricBoundary_comp_zero_apply (f : C2 L) :
    toricBoundary1 (L := L) (toricBoundary2 (L := L) f) = 0 := by
  have h := congrArg (fun T => T f) (toricBoundary_comp_zero (L := L))
  simpa using h

end Lattice
end Stabilizer
end Quantum

