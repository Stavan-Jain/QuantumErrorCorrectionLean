import Mathlib.Tactic

/-!
# Rotated-surface-code cell complex types

Type-level scaffolding for the parametric `RotatedSurfaceCodeN`, paralleling the
toric `CellComplexTypes`. For an `L × L` rotated surface code (intended `L` odd,
`L ≥ 3`):

* `VtxIdx L = Fin L × Fin L` — data qubits, indexed `(x, y)` with `x` the column
  (`0 = leftmost`) and `y` the row (`0 = topmost`).
* `ZFaceIdx L` / `XFaceIdx L` — Z- and X-stabilizer slots, each split into three
  constructors: interior 2×2 face, plus two opposite-edge boundary weight-2
  stabs. Their union has the standard `(L² − 1)/2` count for `L` odd.

The interior face at corner `(x, y) ∈ Fin (L-1) × Fin (L-1)` covers the four
qubits `(x, y), (x+1, y), (x, y+1), (x+1, y+1)`. Its colour alternates with
`(x + y) mod 2`: **Z if even, X if odd**. Boundary stabs are placed so that the
checkerboard parity closes up; see `zSupport` / `xSupport` for the exact
coordinates.

`zSupport zf` / `xSupport xf` return the `Finset` of qubits each stab acts on.
These are the building blocks for the boundary maps `rscBoundary1` /
`rscBoundary2` in `RotatedSurfaceBoundaryMaps.lean`.

## L = 3 sanity check

At `L = 3` the eight stabs collapse to four interior 2×2 faces (two Z, two X)
and four weight-2 boundary stabs (one each on top/bottom/left/right). The qubit
supports (under row-major indexing `(x, y) ↦ y * L + x`) are documented
case-by-case below; they match the existing `RotatedSurfaceCode3.lean`
generators **up to a fixed permutation of qubit indices**. The
retire-equivalence (Stage 8 of the Phase-3 plan) handles that permutation
explicitly.
-/

namespace Quantum
namespace Stabilizer
namespace Lattice
namespace RotatedSurface

open scoped BigOperators

/-- Data qubits on an `L × L` rotated surface code, indexed `(x, y)` with `x`
the column (`0 = leftmost`) and `y` the row (`0 = topmost`). -/
abbrev VtxIdx (L : ℕ) : Type := Fin L × Fin L

/-- 1-chains: `ZMod 2`-valued functions on data qubits. -/
abbrev C1 (L : ℕ) : Type := VtxIdx L → ZMod 2

/-- Top-left corner of an interior 2×2 face. Such a face covers qubits
`(x, y), (x+1, y), (x, y+1), (x+1, y+1)`, so `x, y ∈ Fin (L-1)`. -/
abbrev FaceCornerIdx (L : ℕ) : Type := Fin (L - 1) × Fin (L - 1)

/-- Interior Z-face corners: `(x + y)` even.  Anchored at `(x, y)`. -/
def ZInteriorCornerIdx (L : ℕ) : Type :=
  { c : FaceCornerIdx L // (c.1.val + c.2.val) % 2 = 0 }

/-- Interior X-face corners: `(x + y)` odd. -/
def XInteriorCornerIdx (L : ℕ) : Type :=
  { c : FaceCornerIdx L // (c.1.val + c.2.val) % 2 = 1 }

instance (L : ℕ) : DecidableEq (ZInteriorCornerIdx L) := Subtype.instDecidableEq
instance (L : ℕ) : DecidableEq (XInteriorCornerIdx L) := Subtype.instDecidableEq
instance (L : ℕ) : Fintype (ZInteriorCornerIdx L) := Subtype.fintype _
instance (L : ℕ) : Fintype (XInteriorCornerIdx L) := Subtype.fintype _

/-- Boundary-stab index for a single rough/smooth edge. There are `(L-1)/2`
boundary stabs per side, parameterised here by `Fin ((L-1)/2)`. -/
abbrev RscBdyIdx (L : ℕ) : Type := Fin ((L - 1) / 2)

/-- Z-stabilizer slots: interior Z-faces ⊕ left-boundary ⊕ right-boundary.

* `interior c` — the 2×2 face anchored at `c`.
* `leftBdy k` — the weight-2 left-edge stab covering `(0, 2k+1), (0, 2k+2)`.
* `rightBdy k` — the weight-2 right-edge stab covering `(L-1, 2k), (L-1, 2k+1)`.

The left-right asymmetry (`+1, +2` vs `+0, +1`) keeps the boundary stabs
parity-aligned with the checkerboard of interior faces.
-/
inductive ZFaceIdx (L : ℕ)
  | interior (c : ZInteriorCornerIdx L) : ZFaceIdx L
  | leftBdy (k : RscBdyIdx L) : ZFaceIdx L
  | rightBdy (k : RscBdyIdx L) : ZFaceIdx L
  deriving DecidableEq

/-- X-stabilizer slots: interior X-faces ⊕ top-boundary ⊕ bottom-boundary.

* `interior c` — the 2×2 face anchored at `c`.
* `topBdy k` — the weight-2 top-edge stab covering `(2k, 0), (2k+1, 0)`.
* `bottomBdy k` — the weight-2 bottom-edge stab covering
  `(2k+1, L-1), (2k+2, L-1)`.
-/
inductive XFaceIdx (L : ℕ)
  | interior (c : XInteriorCornerIdx L) : XFaceIdx L
  | topBdy (k : RscBdyIdx L) : XFaceIdx L
  | bottomBdy (k : RscBdyIdx L) : XFaceIdx L
  deriving DecidableEq

/-- Equivalence to a sum-of-three coproduct, used to derive `Fintype`. -/
def zFaceIdxEquivSum (L : ℕ) :
    ZFaceIdx L ≃ (ZInteriorCornerIdx L ⊕ RscBdyIdx L ⊕ RscBdyIdx L) where
  toFun
    | .interior c => Sum.inl c
    | .leftBdy k => Sum.inr (Sum.inl k)
    | .rightBdy k => Sum.inr (Sum.inr k)
  invFun
    | Sum.inl c => .interior c
    | Sum.inr (Sum.inl k) => .leftBdy k
    | Sum.inr (Sum.inr k) => .rightBdy k
  left_inv := by rintro (_ | _ | _) <;> rfl
  right_inv := by rintro (_ | _ | _) <;> rfl

/-- Equivalence to a sum-of-three coproduct, used to derive `Fintype`. -/
def xFaceIdxEquivSum (L : ℕ) :
    XFaceIdx L ≃ (XInteriorCornerIdx L ⊕ RscBdyIdx L ⊕ RscBdyIdx L) where
  toFun
    | .interior c => Sum.inl c
    | .topBdy k => Sum.inr (Sum.inl k)
    | .bottomBdy k => Sum.inr (Sum.inr k)
  invFun
    | Sum.inl c => .interior c
    | Sum.inr (Sum.inl k) => .topBdy k
    | Sum.inr (Sum.inr k) => .bottomBdy k
  left_inv := by rintro (_ | _ | _) <;> rfl
  right_inv := by rintro (_ | _ | _) <;> rfl

instance (L : ℕ) : Fintype (ZFaceIdx L) :=
  Fintype.ofEquiv _ (zFaceIdxEquivSum L).symm

instance (L : ℕ) : Fintype (XFaceIdx L) :=
  Fintype.ofEquiv _ (xFaceIdxEquivSum L).symm

/-- Cast a `Fin (L-1)` index into `Fin L` (low embedding). -/
@[inline] def cornerLo {L : ℕ} (i : Fin (L - 1)) : Fin L :=
  ⟨i.val, by have := i.isLt; omega⟩

/-- Cast a `Fin (L-1)` index plus one into `Fin L` (high embedding). -/
@[inline] def cornerHi {L : ℕ} (i : Fin (L - 1)) : Fin L :=
  ⟨i.val + 1, by have := i.isLt; omega⟩

/-- The four qubits of the 2×2 face anchored at corner `c`. -/
def faceQubits {L : ℕ} (c : FaceCornerIdx L) : Finset (VtxIdx L) :=
  {(cornerLo c.1, cornerLo c.2),
   (cornerHi c.1, cornerLo c.2),
   (cornerLo c.1, cornerHi c.2),
   (cornerHi c.1, cornerHi c.2)}

/-- Qubits acted on by the Z-stabilizer `zf`. -/
def zSupport {L : ℕ} : ZFaceIdx L → Finset (VtxIdx L)
  | .interior c => faceQubits c.val
  | .leftBdy k =>
      let x0 : Fin L := ⟨0, by have := k.isLt; omega⟩
      let y1 : Fin L := ⟨2 * k.val + 1, by have := k.isLt; omega⟩
      let y2 : Fin L := ⟨2 * k.val + 2, by have := k.isLt; omega⟩
      {(x0, y1), (x0, y2)}
  | .rightBdy k =>
      let xR : Fin L := ⟨L - 1, by have := k.isLt; omega⟩
      let y0 : Fin L := ⟨2 * k.val, by have := k.isLt; omega⟩
      let y1 : Fin L := ⟨2 * k.val + 1, by have := k.isLt; omega⟩
      {(xR, y0), (xR, y1)}

/-- Qubits acted on by the X-stabilizer `xf`. -/
def xSupport {L : ℕ} : XFaceIdx L → Finset (VtxIdx L)
  | .interior c => faceQubits c.val
  | .topBdy k =>
      let y0 : Fin L := ⟨0, by have := k.isLt; omega⟩
      let x0 : Fin L := ⟨2 * k.val, by have := k.isLt; omega⟩
      let x1 : Fin L := ⟨2 * k.val + 1, by have := k.isLt; omega⟩
      {(x0, y0), (x1, y0)}
  | .bottomBdy k =>
      let yB : Fin L := ⟨L - 1, by have := k.isLt; omega⟩
      let x1 : Fin L := ⟨2 * k.val + 1, by have := k.isLt; omega⟩
      let x2 : Fin L := ⟨2 * k.val + 2, by have := k.isLt; omega⟩
      {(x1, yB), (x2, yB)}

/-- Membership in the Z-support of an interior face unfolds to the explicit
four-qubit set. -/
lemma zSupport_interior {L : ℕ} (c : ZInteriorCornerIdx L) :
    zSupport (ZFaceIdx.interior c) = faceQubits c.val := rfl

/-- Membership in the X-support of an interior face unfolds to the explicit
four-qubit set. -/
lemma xSupport_interior {L : ℕ} (c : XInteriorCornerIdx L) :
    xSupport (XFaceIdx.interior c) = faceQubits c.val := rfl

end RotatedSurface
end Lattice
end Stabilizer
end Quantum
