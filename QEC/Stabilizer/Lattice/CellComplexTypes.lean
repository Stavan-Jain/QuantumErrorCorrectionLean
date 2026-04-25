import Mathlib.Tactic
import QEC.Stabilizer.Lattice.FinPeriodic

namespace Quantum
namespace Stabilizer
namespace Lattice

open scoped BigOperators

/-- Vertex indices on an `L × L` toric lattice. -/
abbrev VtxIdx (L : ℕ) : Type := Fin L × Fin L

/-- Face indices on an `L × L` toric lattice. -/
abbrev FaceIdx (L : ℕ) : Type := Fin L × Fin L

/-- Edge indices on an `L × L` toric lattice (horizontal/vertical tagged). -/
inductive EdgeIdx (L : ℕ) where
  | h : Fin L → Fin L → EdgeIdx L
  | v : Fin L → Fin L → EdgeIdx L
deriving DecidableEq, Fintype

/-- 0-chains as `ZMod 2`-valued functions on vertices. -/
abbrev C0 (L : ℕ) : Type := VtxIdx L → ZMod 2

/-- 1-chains as `ZMod 2`-valued functions on edges. -/
abbrev C1 (L : ℕ) : Type := EdgeIdx L → ZMod 2

/-- 2-chains as `ZMod 2`-valued functions on faces. -/
abbrev C2 (L : ℕ) : Type := FaceIdx L → ZMod 2

/-- Coercion helper: a horizontal edge index from coordinates. -/
abbrev hEdgeIdx (L : ℕ) (x y : Fin L) : EdgeIdx L := EdgeIdx.h x y

/-- Coercion helper: a vertical edge index from coordinates. -/
abbrev vEdgeIdx (L : ℕ) (x y : Fin L) : EdgeIdx L := EdgeIdx.v x y

/-- Number of vertices in the toric lattice. -/
@[simp] lemma card_vtxIdx (L : ℕ) : Fintype.card (VtxIdx L) = L * L := by
  simp [VtxIdx]

/-- Number of faces in the toric lattice. -/
@[simp] lemma card_faceIdx (L : ℕ) : Fintype.card (FaceIdx L) = L * L := by
  simp [FaceIdx]

/-- Canonical equivalence between edge tags and a sum of two coordinate pairs. -/
def edgeIdxEquivSum (L : ℕ) : EdgeIdx L ≃ (VtxIdx L ⊕ VtxIdx L) where
  toFun
    | EdgeIdx.h x y => Sum.inl (x, y)
    | EdgeIdx.v x y => Sum.inr (x, y)
  invFun
    | Sum.inl p => EdgeIdx.h p.1 p.2
    | Sum.inr p => EdgeIdx.v p.1 p.2
  left_inv := by intro e; cases e <;> rfl
  right_inv := by intro s; cases s <;> rfl

/-- Number of edges in the toric lattice. -/
@[simp] lemma card_edgeIdx (L : ℕ) : Fintype.card (EdgeIdx L) = 2 * L * L := by
  calc
    Fintype.card (EdgeIdx L) = Fintype.card (VtxIdx L ⊕ VtxIdx L) := by
      exact Fintype.card_congr (edgeIdxEquivSum L)
    _ = L * L + (L * L) := by simp [VtxIdx]
    _ = 2 * L * L := by ring

end Lattice
end Stabilizer
end Quantum

