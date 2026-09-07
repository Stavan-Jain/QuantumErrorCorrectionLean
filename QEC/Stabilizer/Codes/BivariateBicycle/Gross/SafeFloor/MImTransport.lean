/-
# Phase 6: T_y transport — propagating the safe-sector floor along y-translations

The five (resp. thirteen) per-orbit floors cover only the orbit representatives; this module
supplies the symmetry that carries each to its whole translation orbit.  The key fact is that
`seamC` is **y-translation covariant at the chain level** (the x-direction fails — the §9.3
cut-shift — but y holds exactly): `seamC (translate (0,k) ζ) = translate1 (0,k) (seamC ζ)`,
verified by kernel `decide` over `ker ∂₂` (the 64 `kcombo`s) × the 6 shifts,
through the sparse seam form (`seamC_eq_sparse`).

Combined with `chainWeight`'s translation-invariance (`translate1` permutes the 72 qubits) and
`∂₂`'s translation-equivariance (`bbBoundary2Fn_translate`), this gives the **transport
reduction** `floor_shiftYk_combo`: if every coset of `[seamC (kcombo c)]` has weight `≥ 12`,
so does every coset of its `(0,k)`-translate.  Dispatch over the y-orbits then reduces all 63
nonzero classes to the orbit reps.
-/
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.SafeFloor.MImClassify

open Quantum.Stabilizer.Homological.BB
open Quantum.Stabilizer.Homological.BB.LightStab

namespace Quantum.Stabilizer.Homological.BB.LightStab

set_option maxRecDepth 4096

/-! ## §15 The structural translation lemmas -/

/-- `translate1` is additive. -/
theorem translate1_add (c : BaseGroup) (a b : BaseGroup × Fin 2 → ZMod 2) :
    translate1 c (a + b) = translate1 c a + translate1 c b := by funext p; rfl

/-- Composition of base translations. -/
theorem translate_comp (c d : BaseGroup) (f : BaseGroup → ZMod 2) :
    translate c (translate d f) = translate (c + d) f := by
  funext g; simp only [translate]; rw [add_assoc]

/-- Translation by `0` is the identity. -/
theorem translate_zero (f : BaseGroup → ZMod 2) : translate (0 : BaseGroup) f = f := by
  funext g; simp [translate]

/-- **`chainWeight` is translation-invariant**: `translate1 c` permutes the
qubits (`p ↦ (p.1 + c, p.2)` is a bijection), so the support cardinality is
unchanged. -/
theorem chainWeight_translate1 (c : BaseGroup) (v : BaseGroup × Fin 2 → ZMod 2) :
    bb72Complex.chainWeight (translate1 c v) = bb72Complex.chainWeight v := by
  rw [bb72Complex_chainWeight_eq, bb72Complex_chainWeight_eq]
  refine Finset.card_bij' (fun p _ => (p.1 + c, p.2)) (fun q _ => (q.1 - c, q.2)) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, translate1] at ha ⊢
    exact ha
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, translate1] at ha ⊢
    simpa using ha
  · intro a _; simp
  · intro a _; simp

/-- `∂₂ f` is a `(0,k)`-translate of another boundary (the chain-map shuffle).
-/
theorem boundary_shuffle_k (k : ZMod 6) (f : BaseGroup → ZMod 2) :
    bbBoundary2Fn baseA baseB f
      = translate1 ((0,k) : BaseGroup)
          (bbBoundary2Fn baseA baseB (translate ((0,-k) : BaseGroup) f)) := by
  have h0 : ((0,k) + (0,-k) : BaseGroup) = 0 := by simp
  rw [← bbBoundary2Fn_translate, translate_comp, h0, translate_zero]

/-! ## §16 The `seamC` y-covariance and the transport reduction -/

/-- **`seamC` is y-translation covariant** on `ker ∂₂` (the x-direction fails; y
holds at the chain level). Kernel `decide` over the 6 shifts × 64 `kcombo`s. -/
theorem seamC_shiftYk_combo : ∀ (k : ZMod 6) (c0 c1 c2 c3 c4 c5 : ZMod 2),
    seamC (translate ((0,k) : BaseGroup) (kcombo c0 c1 c2 c3 c4 c5))
      = translate1 ((0,k) : BaseGroup) (seamC (kcombo c0 c1 c2 c3 c4 c5)) := by
  have core : ∀ (k : ZMod 6) (c0 c1 c2 c3 c4 c5 : ZMod 2) (q : BaseGroup × Fin 2),
      seamCSparse (translate ((0,k) : BaseGroup) (kcombo c0 c1 c2 c3 c4 c5)) q
        = translate1 ((0,k) : BaseGroup) (seamCSparse (kcombo c0 c1 c2 c3 c4 c5)) q := by
    decide +kernel
  intro k c0 c1 c2 c3 c4 c5
  rw [seamC_eq_sparse, seamC_eq_sparse]
  funext q
  exact core k c0 c1 c2 c3 c4 c5 q

/-- **The transport reduction**: the safe-sector floor for `kcombo c` propagates
to every `(0,k)`-translate of it. (`seamC` covariance ▸ boundary shuffle ▸
`translate1` additivity ▸ `chainWeight` invariance, then re-index `f`.) -/
theorem floor_shiftYk_combo (c0 c1 c2 c3 c4 c5 : ZMod 2) (k : ZMod 6)
    (hf : ∀ f, 12 ≤ bb72Complex.chainWeight
      (seamC (kcombo c0 c1 c2 c3 c4 c5) + bbBoundary2Fn baseA baseB f))
    (f : BaseGroup → ZMod 2) :
    12 ≤ bb72Complex.chainWeight
      (seamC (translate ((0,k) : BaseGroup) (kcombo c0 c1 c2 c3 c4 c5))
        + bbBoundary2Fn baseA baseB f) := by
  rw [seamC_shiftYk_combo k c0 c1 c2 c3 c4 c5, boundary_shuffle_k k f, ← translate1_add,
    chainWeight_translate1]
  exact hf (translate ((0,-k) : BaseGroup) f)

/-! ## §17 General 2-D transport (x and y), via an explicit boundary defect

`seamC` is covariant only in `y` at the chain level; in `x` the §9.3 cut-shift
produces a nonzero boundary defect. Both directions are captured by the single
class-level statement `seamC z' = T_c (seamC z) + ∂₂ δ`, which `floor_transfer`
turns into a floor-transport step (the defect `δ` is absorbed into the
re-indexed free chain `f`). This lets a floor proved for one representative
cover its whole **2-D** translation orbit, reducing the 13 `y`-orbit reps to the
5 full-orbit reps `Y0, Y1, Y4, Y11, Y12`. -/

/-- `∂₂ f` is a `c`-translate of another boundary, for an arbitrary base
translation `c` (the general `boundary_shuffle_k`). -/
theorem boundary_shuffle (c : BaseGroup) (f : BaseGroup → ZMod 2) :
    bbBoundary2Fn baseA baseB f
      = translate1 c (bbBoundary2Fn baseA baseB (translate (-c) f)) := by
  have h0 : (c + (-c) : BaseGroup) = 0 := by simp
  rw [← bbBoundary2Fn_translate, translate_comp, h0, translate_zero]

/-- **General floor transport.** Given the class-level covariance
`seamC z' = T_c (seamC z) + ∂₂ δ` (`δ` the explicit boundary defect) and the
floor for `z`, the floor holds for `z'`. Mirrors `floor_shiftYk_combo`, with the
defect folded into the re-indexed free chain. (For `c` a pure `y`-shift the
defect is `0`; for `x` it is nonzero — see `MImAssembly`.) -/
theorem floor_transfer (z z' : BaseGroup → ZMod 2) (c : BaseGroup) (δ : BaseGroup → ZMod 2)
    (hcov : seamC z' = translate1 c (seamC z) + bbBoundary2Fn baseA baseB δ)
    (hf : ∀ f, 12 ≤ bb72Complex.chainWeight (seamC z + bbBoundary2Fn baseA baseB f))
    (f : BaseGroup → ZMod 2) :
    12 ≤ bb72Complex.chainWeight (seamC z' + bbBoundary2Fn baseA baseB f) := by
  rw [hcov, add_assoc, ← bbBoundary2Fn_add, boundary_shuffle c (δ + f), ← translate1_add,
    chainWeight_translate1]
  exact hf (translate (-c) (δ + f))

end Quantum.Stabilizer.Homological.BB.LightStab
