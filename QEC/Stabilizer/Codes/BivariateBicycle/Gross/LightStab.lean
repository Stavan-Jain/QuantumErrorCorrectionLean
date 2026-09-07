/-
# Light-stabilizer classification (A4 §6.3) — discharging `LightStabilizerClassification`

This module builds toward
`lightStabilizerClassification_holds : LightStabilizerClassification`
(`DangerousSector.lean:528`), the analytic input that makes the dangerous
sector of the gross `[[144,12,12]]` BB code unconditional.

The proof is the CRT-engine classification of A4 §§6.2–6.3, layered as:

  §1  the layer dictionary `d₃` over the torus `Z₃²` (A4 §3 "Layer dictionary"):
      a nonzero `F₂`-function whose `F₄`-valued torus-Fourier support is confined
      to certain Frobenius orbits has a forced minimum weight — a kernel `decide`
      over the 512 functions.  Entries used downstream (one-block lemma, A4 §6.3):
      `d₃({1}) = d₃({3}) = 6`, `d₃({1,3}) = 4`.

  §2  the base ↔ torus reindex bridge.  The CRT iso `BaseGroup = Z₆² ≅ Z₂² × Z₃²`
      (`g ↦ (layer g, torus g)`) lets the per-layer torus slice of a base chain be
      analysed by the dictionary.  Two bridges connect the abstract `CRTFrame`
      machinery to `§1`:
        - Fourier: `V ψⱼ s b = fhat3 (slice b s) (charⱼ)` (the component transform
          at layer `s` IS the torus-Fourier coefficient of the slice);
        - weight:  `bwt b = Σ_s weight3 (slice b s)` (a block's weight is the sum of
          its layer slice weights).

Subsequent sections (the sharp one-block `≥16` bound L4c, the Floor lemma L4b, the
six per-shape leaves, and the endgame transfers) are added incrementally; nothing
in a tracked file carries a `sorry`.

**Conventions (A4 §3, shared with `CRTFrame`).** `ω = 2`, `ω² = 3` in `Fin 4`;
`Z₆ = Z₂ × Z₃` via `a ↦ (a mod 2, a mod 3)`; torus characters
`ψ₀ = 1` (char `(0,0)`, the parity component `V₀`), `ψ₁ = ω^{t_y}` (`(0,1)`),
`ψ₂ = ω^{t_x}` (`(1,0)`), `ψ₃ = ω^{t_x+t_y}` (`(1,1)`), `ψ₄ = ω^{t_x+2t_y}`
(`(1,2)`).  Each nontrivial char generates a size-2 Frobenius orbit `{c, 2c}`
(since `f` is `F₂`-valued: `f̂(2c) = f̂(c)²`), so checking one representative per
orbit suffices for support confinement.
-/
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.CRTFrame
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.DangerousSector

open Quantum.Stabilizer.Homological.BB.CRTFrame

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace LightStab

/-! ## §1 The layer dictionary `d₃` over `Z₃²`

For nonzero `f : Z₃² → F₂` whose `F₄`-valued torus-Fourier support is contained in
an orbit set `W`, the Hamming weight is at least `d₃(W)`.  This is the clean finite
core of the one-block lemma (A4 §6.3): there, every layer of a one-block stabilizer
has Fourier support `⊆ {orbit ψ₁, orbit ψ₃}` (the parity, `ψ₂`, `ψ₄` components are
dead), and the dictionary converts that confinement into a per-layer weight floor.

Support confinement is checked at ONE representative per dead orbit (Frobenius makes
this equivalent to checking the whole orbit, for `F₂`-valued `f`); the representatives
are exactly the `CRTFrame` characters `ψ₀..ψ₄`, so `§2`'s Fourier bridge turns each
check into a condition on `V ψⱼ s b`. -/

/-- The 9 torus cells of `Z₃²`. -/
def cells3 : List (ZMod 3 × ZMod 3) :=
  (List.range 3).flatMap (fun a => (List.range 3).map (fun b => ((a : ZMod 3), (b : ZMod 3))))

/-- The torus character value `ω^{a·t_x + b·t_y}` of direction `c = (a,b)` at cell `t`. -/
def tchar (c t : ZMod 3 × ZMod 3) : Fin 4 := omegaPow (c.1 * t.1 + c.2 * t.2)

/-- The `F₄`-valued torus-Fourier coefficient of `f` at character direction
`c = (a, b)`: `Σ_t f(t) · ω^{a·t_x + b·t_y}` (a char-2 `fadd`-fold over the 9
cells; `ω^k = omegaPow k`). -/
def fhat3 (f : ZMod 3 × ZMod 3 → ZMod 2) (c : ZMod 3 × ZMod 3) : Fin 4 :=
  cells3.foldl (fun acc t => if f t = 1 then fadd acc (tchar c t) else acc) 0

/-- Hamming weight of `f` over the 9 torus cells. -/
def weight3 (f : ZMod 3 × ZMod 3 → ZMod 2) : Nat :=
  (cells3.filter (fun t => decide (f t = 1))).length

/-- "Fourier support `⊆ W`": `f̂` vanishes at every (dead-orbit representative)
character in `dead`. -/
def suppOutsideZero (f : ZMod 3 × ZMod 3 → ZMod 2)
    (dead : List (ZMod 3 × ZMod 3)) : Bool :=
  dead.all (fun c => decide (fhat3 f c = 0))

/-! ### Dead-orbit representatives (one char per orbit excluded from `W`). -/

/-- Dead reps for `W = {ψ₁}`: `ψ₀ (0,0)`, `ψ₂ (1,0)`, `ψ₃ (1,1)`, `ψ₄ (1,2)`. -/
def dead1 : List (ZMod 3 × ZMod 3) := [(0, 0), (1, 0), (1, 1), (1, 2)]
/-- Dead reps for `W = {ψ₃}`: `ψ₀ (0,0)`, `ψ₁ (0,1)`, `ψ₂ (1,0)`, `ψ₄ (1,2)`. -/
def dead3 : List (ZMod 3 × ZMod 3) := [(0, 0), (0, 1), (1, 0), (1, 2)]
/-- Dead reps for `W = {ψ₁,ψ₃}`: `ψ₀ (0,0)`, `ψ₂ (1,0)`, `ψ₄ (1,2)`. -/
def dead13 : List (ZMod 3 × ZMod 3) := [(0, 0), (1, 0), (1, 2)]

/-! ### The kernel-friendly chain constructor.

The dictionary bounds sweep all 512 chains `f : Z₃² → F₂`.  Enumerating that
pi-type directly makes the kernel whnf the pi-`Fintype` instance (the
noncomputable-whnf hazard's finite cousin), so the sweeps are instead stated
over nine `ZMod 2` cell values via `mkTorus`, with `eq_mkTorus` transporting
the result to an arbitrary `f`. -/

/-- Explicit torus chain from its nine cell values (row-major
`(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)`). -/
def mkTorus (v00 v01 v02 v10 v11 v12 v20 v21 v22 : ZMod 2) :
    ZMod 3 × ZMod 3 → ZMod 2 := fun t =>
  if t = (0, 0) then v00 else if t = (0, 1) then v01 else if t = (0, 2) then v02
  else if t = (1, 0) then v10 else if t = (1, 1) then v11 else if t = (1, 2) then v12
  else if t = (2, 0) then v20 else if t = (2, 1) then v21 else v22

/-- Every torus chain is the `mkTorus` of its nine cell values. -/
theorem eq_mkTorus (f : ZMod 3 × ZMod 3 → ZMod 2) :
    f = mkTorus (f (0, 0)) (f (0, 1)) (f (0, 2)) (f (1, 0)) (f (1, 1)) (f (1, 2))
        (f (2, 0)) (f (2, 1)) (f (2, 2)) := by
  have h3 : ∀ x : ZMod 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
  funext t
  obtain ⟨t1, t2⟩ := t
  rcases h3 t1 with rfl | rfl | rfl <;> rcases h3 t2 with rfl | rfl | rfl <;> rfl

/-! ### The three dictionary lower bounds (512-chain kernel sweeps via
`mkTorus`).  These are the exact `d₃`-costs the one-block lemma (A4 §6.3)
consumes. -/

/-- `d₃({1}) = 6`: a nonzero `f` with Fourier support `⊆ orbit(ψ₁)` has weight `≥ 6`. -/
theorem d3_psi1_ge6 : ∀ f : ZMod 3 × ZMod 3 → ZMod 2,
    f ≠ 0 → suppOutsideZero f dead1 = true → 6 ≤ weight3 f := by
  have key : ∀ v00 v01 v02 v10 v11 v12 v20 v21 v22 : ZMod 2,
      mkTorus v00 v01 v02 v10 v11 v12 v20 v21 v22 ≠ 0 →
      suppOutsideZero (mkTorus v00 v01 v02 v10 v11 v12 v20 v21 v22) dead1 = true →
      6 ≤ weight3 (mkTorus v00 v01 v02 v10 v11 v12 v20 v21 v22) := by decide +kernel
  intro f hne hsupp
  rw [eq_mkTorus f] at hne hsupp ⊢
  exact key _ _ _ _ _ _ _ _ _ hne hsupp

/-- `d₃({3}) = 6`: a nonzero `f` with Fourier support `⊆ orbit(ψ₃)` has weight `≥ 6`. -/
theorem d3_psi3_ge6 : ∀ f : ZMod 3 × ZMod 3 → ZMod 2,
    f ≠ 0 → suppOutsideZero f dead3 = true → 6 ≤ weight3 f := by
  have key : ∀ v00 v01 v02 v10 v11 v12 v20 v21 v22 : ZMod 2,
      mkTorus v00 v01 v02 v10 v11 v12 v20 v21 v22 ≠ 0 →
      suppOutsideZero (mkTorus v00 v01 v02 v10 v11 v12 v20 v21 v22) dead3 = true →
      6 ≤ weight3 (mkTorus v00 v01 v02 v10 v11 v12 v20 v21 v22) := by decide +kernel
  intro f hne hsupp
  rw [eq_mkTorus f] at hne hsupp ⊢
  exact key _ _ _ _ _ _ _ _ _ hne hsupp

/-- `d₃({1,3}) = 4`: a nonzero `f` with Fourier support `⊆ orbit(ψ₁) ∪ orbit(ψ₃)`
has weight `≥ 4`. -/
theorem d3_psi1or3_ge4 : ∀ f : ZMod 3 × ZMod 3 → ZMod 2,
    f ≠ 0 → suppOutsideZero f dead13 = true → 4 ≤ weight3 f := by
  have key : ∀ v00 v01 v02 v10 v11 v12 v20 v21 v22 : ZMod 2,
      mkTorus v00 v01 v02 v10 v11 v12 v20 v21 v22 ≠ 0 →
      suppOutsideZero (mkTorus v00 v01 v02 v10 v11 v12 v20 v21 v22) dead13 = true →
      4 ≤ weight3 (mkTorus v00 v01 v02 v10 v11 v12 v20 v21 v22) := by decide +kernel
  intro f hne hsupp
  rw [eq_mkTorus f] at hne hsupp ⊢
  exact key _ _ _ _ _ _ _ _ _ hne hsupp

/-! ### Tightness: each bound is attained (guards against a vacuously-true,
over-constrained support predicate).  Witnesses: `d₃({1})` — the two rows
`t_y ∈ {0,1}`; `d₃({3})` — the two diagonals `t_x+t_y ∈ {0,1}`; `d₃({1,3})` —
their symmetric difference (weight 4). -/

theorem d3_psi1_tight : ∃ f : ZMod 3 × ZMod 3 → ZMod 2,
    f ≠ 0 ∧ suppOutsideZero f dead1 = true ∧ weight3 f = 6 :=
  ⟨mkTorus 1 1 0 1 1 0 1 1 0, by decide, by decide, by decide⟩

theorem d3_psi3_tight : ∃ f : ZMod 3 × ZMod 3 → ZMod 2,
    f ≠ 0 ∧ suppOutsideZero f dead3 = true ∧ weight3 f = 6 :=
  ⟨mkTorus 1 1 0 1 0 1 0 1 1, by decide, by decide, by decide⟩

theorem d3_psi1or3_tight : ∃ f : ZMod 3 × ZMod 3 → ZMod 2,
    f ≠ 0 ∧ suppOutsideZero f dead13 = true ∧ weight3 f = 4 :=
  ⟨mkTorus 0 0 0 0 1 1 1 0 1, by decide, by decide, by decide⟩

/-! ## §2 The base ↔ torus reindex bridge

`BaseGroup = Z₆² ≅ Z₂² × Z₃²` via `g ↦ (layer g, torus g)`; `combineCell` is the
inverse (CRT: `3·s + 4·t (mod 6)` per coordinate).  The layer-`s` torus slice of a
base chain `b` is `slice b s := fun t => b (combineCell s t)`. -/

/-- CRT inverse on one `Z₆` coordinate: the element `≡ s (mod 2)`, `≡ t (mod 3)`. -/
def combine1 (s : ZMod 2) (t : ZMod 3) : ZMod 6 := ((3 * s.val + 4 * t.val : ℕ) : ZMod 6)

/-- CRT inverse `Z₂² × Z₃² → Z₆² = BaseGroup`. -/
def combineCell (s : ZMod 2 × ZMod 2) (t : ZMod 3 × ZMod 3) : BaseGroup :=
  (combine1 s.1 t.1, combine1 s.2 t.2)

/-- The layer-`s` torus slice of a base chain `b`, as a `Z₃² → F₂` function. -/
def slice (b : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) : ZMod 3 × ZMod 3 → ZMod 2 :=
  fun t => b (combineCell s t)

/-! ### Round-trip facts (finite `decide`). -/

theorem layer_combineCell : ∀ (s : ZMod 2 × ZMod 2) (t : ZMod 3 × ZMod 3),
    layer (combineCell s t) = s := by decide
theorem torus_combineCell : ∀ (s : ZMod 2 × ZMod 2) (t : ZMod 3 × ZMod 3),
    torus (combineCell s t) = t := by decide
theorem combineCell_layer_torus : ∀ g : BaseGroup,
    combineCell (layer g) (torus g) = g := by decide
theorem cells3_complete : ∀ t : ZMod 3 × ZMod 3, t ∈ cells3 := by decide

/-! ### `fhat3` is `F₂`-linear (the bridge needs additivity to lift the basis case). -/

/-- `fhat3` is `F₂`-additive in the chain. -/
theorem fhat3_add (f g : ZMod 3 × ZMod 3 → ZMod 2) (c : ZMod 3 × ZMod 3) :
    fhat3 (f + g) c = fadd (fhat3 f c) (fhat3 g c) := by
  have step : ∀ (a b : ZMod 2) (Y W z : Fin 4),
      (if a + b = 1 then fadd (fadd Y W) z else fadd Y W)
        = fadd (if a = 1 then fadd Y z else Y) (if b = 1 then fadd W z else W) := by decide
  have gen : ∀ (L : List (ZMod 3 × ZMod 3)) (aF aG : Fin 4),
      L.foldl (fun acc t => if (f + g) t = 1 then fadd acc (tchar c t) else acc) (fadd aF aG)
        = fadd (L.foldl (fun acc t => if f t = 1 then fadd acc (tchar c t) else acc) aF)
               (L.foldl (fun acc t => if g t = 1 then fadd acc (tchar c t) else acc) aG) := by
    intro L
    induction L with
    | nil => intro aF aG; rfl
    | cons h t ih =>
      intro aF aG
      rw [List.foldl_cons, List.foldl_cons, List.foldl_cons]
      have hhead : (if (f + g) h = 1 then fadd (fadd aF aG) (tchar c h) else fadd aF aG)
          = fadd (if f h = 1 then fadd aF (tchar c h) else aF)
                 (if g h = 1 then fadd aG (tchar c h) else aG) := by
        rw [Pi.add_apply]; exact step (f h) (g h) aF aG _
      rw [hhead]
      exact ih _ _
  have h00 : fadd (0 : Fin 4) 0 = 0 := by decide
  have := gen cells3 0 0
  rw [h00] at this
  simpa [fhat3] using this

theorem fhat3_zero (c : ZMod 3 × ZMod 3) : fhat3 (0 : ZMod 3 × ZMod 3 → ZMod 2) c = 0 := by
  have h := fhat3_add 0 0 c
  rw [add_zero] at h
  exact (fadd_self (fhat3 0 c) ▸ h)

theorem slice_zero (s : ZMod 2 × ZMod 2) : slice (0 : BaseGroup → ZMod 2) s = 0 := by
  funext t; rfl

theorem slice_add (a b : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) :
    slice (a + b) s = slice a s + slice b s := by
  funext t; rfl

/-! ### The Fourier bridge `V ψⱼ s b = fhat3 (slice b s) (charⱼ)`.
Both sides are `F₂`-additive in `b` and agree on every `δ_g` (kernel `decide`
over the 36 `g` × 4 `s` — both sides are explicit `List.foldl`s, so the direct
statement is already kernel-checkable), hence agree for all `b`. -/

/-- Two `F₂`-additive maps `(BaseGroup → ZMod 2) → Fin 4` that agree on every `δ_g`
agree everywhere. -/
theorem fourier_bridge_gen (M N : (BaseGroup → ZMod 2) → Fin 4)
    (hM0 : M 0 = 0) (hN0 : N 0 = 0)
    (hMadd : ∀ a b, M (a + b) = fadd (M a) (M b))
    (hNadd : ∀ a b, N (a + b) = fadd (N a) (N b))
    (hbasis : ∀ g, M (Pi.single g 1) = N (Pi.single g 1)) (b : BaseGroup → ZMod 2) :
    M b = N b := by
  have key : ∀ S : Finset BaseGroup, M (ind S) = N (ind S) := by
    intro S
    induction S using Finset.induction with
    | empty => rw [ind_empty, hM0, hN0]
    | @insert p S hp ih => rw [ind_insert hp, hMadd, hNadd, hbasis p, ih]
  rw [self_eq_ind_filter b]
  exact key _

theorem Nadd (s : ZMod 2 × ZMod 2) (c : ZMod 3 × ZMod 3) (a b : BaseGroup → ZMod 2) :
    fhat3 (slice (a + b) s) c = fadd (fhat3 (slice a s) c) (fhat3 (slice b s) c) := by
  rw [slice_add]; exact fhat3_add _ _ _

theorem Nzero (s : ZMod 2 × ZMod 2) (c : ZMod 3 × ZMod 3) :
    fhat3 (slice (0 : BaseGroup → ZMod 2) s) c = 0 := by rw [slice_zero, fhat3_zero]

theorem basis_agree0 : ∀ (g : BaseGroup) (s : ZMod 2 × ZMod 2),
    V psi0 s (Pi.single g 1) = fhat3 (slice (Pi.single g 1) s) (0, 0) := by decide +kernel
theorem basis_agree1 : ∀ (g : BaseGroup) (s : ZMod 2 × ZMod 2),
    V psi1 s (Pi.single g 1) = fhat3 (slice (Pi.single g 1) s) (0, 1) := by decide +kernel
theorem basis_agree2 : ∀ (g : BaseGroup) (s : ZMod 2 × ZMod 2),
    V psi2 s (Pi.single g 1) = fhat3 (slice (Pi.single g 1) s) (1, 0) := by decide +kernel
theorem basis_agree3 : ∀ (g : BaseGroup) (s : ZMod 2 × ZMod 2),
    V psi3 s (Pi.single g 1) = fhat3 (slice (Pi.single g 1) s) (1, 1) := by decide +kernel
theorem basis_agree4 : ∀ (g : BaseGroup) (s : ZMod 2 × ZMod 2),
    V psi4 s (Pi.single g 1) = fhat3 (slice (Pi.single g 1) s) (1, 2) := by decide +kernel

/-- Fourier bridge, `ψ₀` (parity). -/
theorem fourier_bridge0 (b : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) :
    V psi0 s b = fhat3 (slice b s) (0, 0) :=
  fourier_bridge_gen (V psi0 s) (fun b => fhat3 (slice b s) (0, 0))
    (V_zero psi0 s) (Nzero s (0,0)) (V_add psi0 s) (Nadd s (0,0)) (fun g => basis_agree0 g s) b
/-- Fourier bridge, `ψ₁`. -/
theorem fourier_bridge1 (b : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) :
    V psi1 s b = fhat3 (slice b s) (0, 1) :=
  fourier_bridge_gen (V psi1 s) (fun b => fhat3 (slice b s) (0, 1))
    (V_zero psi1 s) (Nzero s (0,1)) (V_add psi1 s) (Nadd s (0,1)) (fun g => basis_agree1 g s) b
/-- Fourier bridge, `ψ₂`. -/
theorem fourier_bridge2 (b : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) :
    V psi2 s b = fhat3 (slice b s) (1, 0) :=
  fourier_bridge_gen (V psi2 s) (fun b => fhat3 (slice b s) (1, 0))
    (V_zero psi2 s) (Nzero s (1,0)) (V_add psi2 s) (Nadd s (1,0)) (fun g => basis_agree2 g s) b
/-- Fourier bridge, `ψ₃`. -/
theorem fourier_bridge3 (b : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) :
    V psi3 s b = fhat3 (slice b s) (1, 1) :=
  fourier_bridge_gen (V psi3 s) (fun b => fhat3 (slice b s) (1, 1))
    (V_zero psi3 s) (Nzero s (1,1)) (V_add psi3 s) (Nadd s (1,1)) (fun g => basis_agree3 g s) b
/-- Fourier bridge, `ψ₄`. -/
theorem fourier_bridge4 (b : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) :
    V psi4 s b = fhat3 (slice b s) (1, 2) :=
  fourier_bridge_gen (V psi4 s) (fun b => fhat3 (slice b s) (1, 2))
    (V_zero psi4 s) (Nzero s (1,2)) (V_add psi4 s) (Nadd s (1,2)) (fun g => basis_agree4 g s) b

/-! ### The weight bridge `bwt b = Σ_s weight3 (slice b s)`. -/

/-- List weight `weight3` equals the `Finset.card` of the support. -/
theorem weight3_eq_card (f : ZMod 3 × ZMod 3 → ZMod 2) :
    weight3 f = (Finset.univ.filter (fun t => f t = 1)).card := by
  have hnd : cells3.Nodup := by decide
  unfold weight3
  rw [← List.toFinset_card_of_nodup (hnd.filter _)]
  congr 1
  ext t
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, Finset.mem_filter,
    Finset.mem_univ, true_and, and_iff_right_iff_imp]
  intro _; exact cells3_complete t

/-- The CRT equivalence `BaseGroup ≃ Z₂² × Z₃²`, `g ↦ (layer g, torus g)`. -/
def baseEquiv : BaseGroup ≃ (ZMod 2 × ZMod 2) × (ZMod 3 × ZMod 3) where
  toFun g := (layer g, torus g)
  invFun st := combineCell st.1 st.2
  left_inv g := combineCell_layer_torus g
  right_inv st := by
    obtain ⟨s, t⟩ := st
    have h1 := layer_combineCell s t
    have h2 := torus_combineCell s t
    simp only [Prod.mk.injEq]
    exact ⟨h1, h2⟩

/-- The base weight of a block `b`, as a `Finset.card`. -/
def bwt (b : BaseGroup → ZMod 2) : Nat := (Finset.univ.filter (fun h => b h = 1)).card

/-- **The weight bridge**: a block's weight is the sum over layers of its torus slice
weights. -/
theorem weight_bridge (b : BaseGroup → ZMod 2) :
    bwt b = ∑ s : ZMod 2 × ZMod 2, weight3 (slice b s) := by
  unfold bwt
  simp only [weight3_eq_card, Finset.card_filter]
  rw [← Equiv.sum_comp baseEquiv.symm (fun h => if b h = 1 then 1 else 0)]
  rw [Fintype.sum_prod_type]
  rfl

/-! ## §3 The sharp one-block lemma (L4c)

`w ∈ Ann(A) ∖ ker ∂₂` (`A·w = 0`, `B·w ≠ 0`) ⟹ `|B·w| ≥ 16` (A4 §6.3, one-block
lemma, sharp form).  This is the completeness-free route: a forward implication
from `A·w = 0` via multiplicativity + the engine (the Fourier profile of `B·w`) and
the `§1`/`§2` dictionary + bridge (the per-layer weight floor).  The sharp `16` (not
the old `≥ 12`) is what closes the d=12 gap at exactly 12 in the endgame transfers.

`CRTFrame` supplies the radical-multiplier multiplicativity (`mult_A1/A3/A4`,
`mult_B2/B3/B4`); the unit components (`Â₀=Â₂=B̂₀=B̂₁=1+u+v`) are completed here. -/

/-- The unit multiplier value vector `Â₀ = Â₂ = B̂₀ = B̂₁ = 1+u+v = (1,1,1,0)`. -/
def unitHat : Ring := fun s =>
  if s = (0, 0) then 1 else if s = (1, 0) then 1 else if s = (0, 1) then 1 else 0

/-- `V₀(A⋆z) = Â₀·V₀(z)`, `Â₀ = unitHat`. -/
theorem mult_A0 (z : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) :
    V psi0 s (baseA ⋆ z) = rmul unitHat (fun s' => V psi0 s' z) s :=
  mult_of_basis psi0 baseA unitHat (basis_of_translate (by decide +kernel)) z s
/-- `V₂(A⋆z) = Â₂·V₂(z)`, `Â₂ = unitHat`. -/
theorem mult_A2 (z : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) :
    V psi2 s (baseA ⋆ z) = rmul unitHat (fun s' => V psi2 s' z) s :=
  mult_of_basis psi2 baseA unitHat (basis_of_translate (by decide +kernel)) z s
/-- `V₀(B⋆z) = B̂₀·V₀(z)`, `B̂₀ = unitHat`. -/
theorem mult_B0 (z : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) :
    V psi0 s (baseB ⋆ z) = rmul unitHat (fun s' => V psi0 s' z) s :=
  mult_of_basis psi0 baseB unitHat (basis_of_translate (by decide +kernel)) z s
/-- `V₁(B⋆z) = B̂₁·V₁(z)`, `B̂₁ = unitHat`. -/
theorem mult_B1 (z : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) :
    V psi1 s (baseB ⋆ z) = rmul unitHat (fun s' => V psi1 s' z) s :=
  mult_of_basis psi1 baseB unitHat (basis_of_translate (by decide +kernel)) z s

/-! ### Ring facts for the Fourier profile of `B·w` (kernel `decide` over the
256-element ring, swept through `mkRing`/`ring_eq_mkRing` so the kernel never
whnfs the pi-type `Fintype` of `Ring`). -/

/-- `V₂`: a `unitHat`-annihilated component is killed by `B̂₂` too. -/
theorem unitHat_zero_to_Bhat2 : ∀ r : Ring,
    rmul unitHat r = (fun _ => 0) → rmul Bhat2 r = (fun _ => 0) := by
  have key : ∀ a b c d : Fin 4,
      rmul unitHat (mkRing a b c d) = (fun _ => 0) →
      rmul Bhat2 (mkRing a b c d) = (fun _ => 0) := by decide +kernel
  intro r
  rw [ring_eq_mkRing r]
  exact key _ _ _ _

/-- `V₄`: an `Â₄`-annihilated component is killed by `B̂₂` (since `B̂₄ = ω·Â₄`). -/
theorem Ahat4_zero_to_Bhat2 : ∀ r : Ring,
    rmul Ahat4 r = (fun _ => 0) → rmul Bhat2 r = (fun _ => 0) := by
  have key : ∀ a b c d : Fin 4,
      rmul Ahat4 (mkRing a b c d) = (fun _ => 0) →
      rmul Bhat2 (mkRing a b c d) = (fun _ => 0) := by decide +kernel
  intro r
  rw [ring_eq_mkRing r]
  exact key _ _ _ _

/-- `V₃`: an `Â₁`-annihilated component, hit by `B̂₂`, lands in the socle — a
constant vector, i.e. `0` or everywhere-nonzero. -/
theorem Ahat1_zero_Bhat2_const : ∀ r : Ring,
    rmul Ahat1 r = (fun _ => 0) →
    rmul Bhat2 r = (fun _ => 0) ∨ (∀ s, rmul Bhat2 r s ≠ 0) := by
  have key : ∀ a b c d : Fin 4,
      rmul Ahat1 (mkRing a b c d) = (fun _ => 0) →
      rmul Bhat2 (mkRing a b c d) = (fun _ => 0) ∨
        (∀ s, rmul Bhat2 (mkRing a b c d) s ≠ 0) := by decide +kernel
  intro r
  rw [ring_eq_mkRing r]
  exact key _ _ _ _

/-- `V₁`: `rmul unitHat r` stays in `Ann(Â₁)` when `r` does (`B̂₁` is a unit). -/
theorem Ahat1_unitHat_ann : ∀ r : Ring,
    rmul Ahat1 r = (fun _ => 0) → rmul Ahat1 (rmul unitHat r) = (fun _ => 0) := by
  have key : ∀ a b c d : Fin 4,
      rmul Ahat1 (mkRing a b c d) = (fun _ => 0) →
      rmul Ahat1 (rmul unitHat (mkRing a b c d)) = (fun _ => 0) := by decide +kernel
  intro r
  rw [ring_eq_mkRing r]
  exact key _ _ _ _

/-- `V₁` structure: a nonzero `Ann(Â₁)` element has `≥ 3` nonzero layers. -/
theorem annAhat1_zero_or_ge3 : ∀ r : Ring,
    rmul Ahat1 r = (fun _ => 0) → r = (fun _ => 0) ∨ nLayers r ≥ 3 := by
  have key : ∀ a b c d : Fin 4,
      rmul Ahat1 (mkRing a b c d) = (fun _ => 0) →
      mkRing a b c d = (fun _ => 0) ∨ nLayers (mkRing a b c d) ≥ 3 := by decide +kernel
  intro r
  rw [ring_eq_mkRing r]
  exact key _ _ _ _

/-! ### Layer-count and Fourier-injectivity helpers. -/

theorem allS_complete : ∀ s : ZMod 2 × ZMod 2, s ∈ allS := by decide

/-- `nLayers` (a `List` length) equals the `Finset.card` of the nonzero layers. -/
theorem nLayers_eq_card (p : Ring) :
    nLayers p = (Finset.univ.filter (fun s => p s ≠ 0)).card := by
  have hnd : allS.Nodup := by decide
  unfold nLayers
  rw [← List.toFinset_card_of_nodup (hnd.filter _)]
  congr 1
  ext s
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, Finset.mem_filter,
    Finset.mem_univ, true_and, and_iff_right_iff_imp]
  intro _; exact allS_complete s

/-- Torus-Fourier injectivity at the 5 orbit reps (contrapositive form): a nonzero
function has a nonzero `fhat3` at some representative (kernel `decide` over the
512 chains, via `mkTorus`). -/
theorem fhat3_nonzero_reps : ∀ f : ZMod 3 × ZMod 3 → ZMod 2, f ≠ 0 →
    fhat3 f (0, 0) ≠ 0 ∨ fhat3 f (0, 1) ≠ 0 ∨ fhat3 f (1, 0) ≠ 0 ∨
    fhat3 f (1, 1) ≠ 0 ∨ fhat3 f (1, 2) ≠ 0 := by
  have key : ∀ v00 v01 v02 v10 v11 v12 v20 v21 v22 : ZMod 2,
      mkTorus v00 v01 v02 v10 v11 v12 v20 v21 v22 ≠ 0 →
      fhat3 (mkTorus v00 v01 v02 v10 v11 v12 v20 v21 v22) (0, 0) ≠ 0 ∨
      fhat3 (mkTorus v00 v01 v02 v10 v11 v12 v20 v21 v22) (0, 1) ≠ 0 ∨
      fhat3 (mkTorus v00 v01 v02 v10 v11 v12 v20 v21 v22) (1, 0) ≠ 0 ∨
      fhat3 (mkTorus v00 v01 v02 v10 v11 v12 v20 v21 v22) (1, 1) ≠ 0 ∨
      fhat3 (mkTorus v00 v01 v02 v10 v11 v12 v20 v21 v22) (1, 2) ≠ 0 := by decide +kernel
  intro f hne
  rw [eq_mkTorus f] at hne ⊢
  exact key _ _ _ _ _ _ _ _ _ hne

/-- If every layer slice of `b` is zero then `b` is zero. -/
theorem b_zero_of_slices (b : BaseGroup → ZMod 2) (h : ∀ s, slice b s = 0) : b = 0 := by
  funext g
  have := congrFun (h (layer g)) (torus g)
  rwa [slice, combineCell_layer_torus] at this

/-- Core: a block `b` with the Fourier profile of `B·w` (`w ∈ Ann(A)`) — `V₀=V₂=V₄=0`,
`V₃` constant, `V₁ ∈ Ann(Â₁)` — has weight `≥ 16`. -/
theorem oneBlock_core (b : BaseGroup → ZMod 2)
    (hV0 : ∀ s, V psi0 s b = 0) (hV2 : ∀ s, V psi2 s b = 0) (hV4 : ∀ s, V psi4 s b = 0)
    (hV3 : (∀ s, V psi3 s b = 0) ∨ (∀ s, V psi3 s b ≠ 0))
    (hV1ann : rmul Ahat1 (fun s => V psi1 s b) = (fun _ => 0))
    (hbne : b ≠ 0) : 16 ≤ bwt b := by
  have hf00 : ∀ s, fhat3 (slice b s) (0, 0) = 0 := fun s => (fourier_bridge0 b s).symm.trans (hV0 s)
  have hf10 : ∀ s, fhat3 (slice b s) (1, 0) = 0 := fun s => (fourier_bridge2 b s).symm.trans (hV2 s)
  have hf12 : ∀ s, fhat3 (slice b s) (1, 2) = 0 := fun s => (fourier_bridge4 b s).symm.trans (hV4 s)
  have hsupp13 : ∀ s, suppOutsideZero (slice b s) dead13 = true := by
    intro s
    unfold suppOutsideZero dead13
    rw [List.all_eq_true]
    intro c hc
    rw [decide_eq_true_eq]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hf00 s
    · exact hf10 s
    · exact hf12 s
  have hsl_ne : ∀ s, (V psi1 s b ≠ 0 ∨ V psi3 s b ≠ 0) → slice b s ≠ 0 := by
    intro s hor hsl
    rcases hor with h | h
    · exact h (by rw [fourier_bridge1 b s, hsl, fhat3_zero])
    · exact h (by rw [fourier_bridge3 b s, hsl, fhat3_zero])
  rw [weight_bridge]
  rcases hV3 with h3z | h3nz
  · -- V₃ ≡ 0: b ≠ 0 forces V₁ ≠ 0, which has ≥ 3 nonzero layers, each costing ≥ 6.
    have hV1ne : (fun s => V psi1 s b) ≠ (fun _ => 0) := by
      intro h1z
      apply hbne
      apply b_zero_of_slices
      intro s
      by_contra hsl
      have hb01 : fhat3 (slice b s) (0, 1) = 0 :=
        (fourier_bridge1 b s).symm.trans (congrFun h1z s)
      have hb11 : fhat3 (slice b s) (1, 1) = 0 := (fourier_bridge3 b s).symm.trans (h3z s)
      rcases fhat3_nonzero_reps (slice b s) hsl with h | h | h | h | h
      · exact h (hf00 s)
      · exact h hb01
      · exact h (hf10 s)
      · exact h hb11
      · exact h (hf12 s)
    have hn1 : 3 ≤ nLayers (fun s => V psi1 s b) := by
      rcases annAhat1_zero_or_ge3 _ hV1ann with h | h
      · exact absurd h hV1ne
      · exact h
    have hfloor : ∀ s, 6 * (if V psi1 s b ≠ 0 then 1 else 0) ≤ weight3 (slice b s) := by
      intro s
      by_cases hv1 : V psi1 s b ≠ 0
      · rw [if_pos hv1, mul_one]
        refine d3_psi1_ge6 (slice b s) (hsl_ne s (Or.inl hv1)) ?_
        have h11 : fhat3 (slice b s) (1, 1) = 0 := (fourier_bridge3 b s).symm.trans (h3z s)
        unfold suppOutsideZero dead1
        rw [List.all_eq_true]
        intro c hc
        rw [decide_eq_true_eq]
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl
        · exact hf00 s
        · exact hf10 s
        · exact h11
        · exact hf12 s
      · rw [if_neg hv1, mul_zero]; exact Nat.zero_le _
    calc 16 ≤ 6 * nLayers (fun s => V psi1 s b) := by omega
      _ = 6 * (Finset.univ.filter (fun s => V psi1 s b ≠ 0)).card := by rw [nLayers_eq_card]
      _ = ∑ s : ZMod 2 × ZMod 2, 6 * (if V psi1 s b ≠ 0 then 1 else 0) := by
            rw [Finset.card_filter, Finset.mul_sum]
      _ ≤ ∑ s : ZMod 2 × ZMod 2, weight3 (slice b s) := Finset.sum_le_sum (fun s _ => hfloor s)
  · -- V₃ everywhere nonzero: every slice nonzero, each costing ≥ 4.
    have hfloor4 : ∀ s, 4 ≤ weight3 (slice b s) := fun s =>
      d3_psi1or3_ge4 (slice b s) (hsl_ne s (Or.inr (h3nz s))) (hsupp13 s)
    have h4 : ∑ _s : ZMod 2 × ZMod 2, (4 : ℕ) = 16 := by
      rw [Finset.sum_const, Finset.card_univ]; rfl
    calc (16 : ℕ) = ∑ _s : ZMod 2 × ZMod 2, 4 := h4.symm
      _ ≤ ∑ s : ZMod 2 × ZMod 2, weight3 (slice b s) := Finset.sum_le_sum (fun s _ => hfloor4 s)

/-- **The sharp one-block lemma (L4c)**: `w ∈ Ann(A) ∖ ker ∂₂` (`A·w = 0`, `B·w ≠ 0`)
forces `|B·w| ≥ 16`. -/
theorem oneBlock_ge16 (w : BaseGroup → ZMod 2) (hA : baseA ⋆ w = 0)
    (hB : baseB ⋆ w ≠ 0) : 16 ≤ bwt (baseB ⋆ w) := by
  apply oneBlock_core (baseB ⋆ w)
  · intro s
    have hkey : rmul unitHat (fun s' => V psi0 s' w) = (fun _ => 0) := by
      funext s'; rw [← mult_A0 w s', hA]; exact V_zero psi0 s'
    rw [mult_B0 w s, hkey]
  · intro s
    have hkeyU : rmul unitHat (fun s' => V psi2 s' w) = (fun _ => 0) := by
      funext s'; rw [← mult_A2 w s', hA]; exact V_zero psi2 s'
    rw [mult_B2 w s, unitHat_zero_to_Bhat2 _ hkeyU]
  · intro s
    have hkeyA : rmul Ahat4 (fun s' => V psi4 s' w) = (fun _ => 0) := by
      funext s'; rw [← mult_A4 w s', hA]; exact V_zero psi4 s'
    rw [mult_B4 w s, Ahat4_zero_to_Bhat2 _ hkeyA]
  · have hkey3 : rmul Ahat1 (fun s' => V psi3 s' w) = (fun _ => 0) := by
      funext s'; rw [← mult_A3 w s', hA]; exact V_zero psi3 s'
    rcases Ahat1_zero_Bhat2_const _ hkey3 with h | h
    · left; intro s; rw [mult_B3 w s]; exact congrFun h s
    · right; intro s; rw [mult_B3 w s]; exact h s
  · have hkey1 : rmul Ahat1 (fun s' => V psi1 s' w) = (fun _ => 0) := by
      funext s'; rw [← mult_A1 w s', hA]; exact V_zero psi1 s'
    have hb1 : (fun s => V psi1 s (baseB ⋆ w)) = rmul unitHat (fun s' => V psi1 s' w) := by
      funext s; exact mult_B1 w s
    rw [hb1]; exact Ahat1_unitHat_ann _ hkey1
  · exact hB

/-! ## §4 Endgame transfer (block → boundary)

L4c, contrapositive, lifts a block-level match to the full boundary: if the A-block
of `∂₂f` equals a hexagon/D-pair A-block, the residual `w = f − witness ∈ Ann(A)`
has `|B·w| < 16`, so (L4c) `B·w = 0` and `∂₂f = ∂₂(witness)`. -/

/-- L4c contrapositive: `w ∈ Ann(A)` with `|B·w| < 16` forces `B·w = 0`. -/
theorem oneBlock_contra (w : BaseGroup → ZMod 2) (hA : baseA ⋆ w = 0)
    (hlt : bwt (baseB ⋆ w) < 16) : baseB ⋆ w = 0 := by
  by_contra hne
  exact absurd (oneBlock_ge16 w hA hne) (Nat.not_le.mpr hlt)

/-- Hamming weight (`bwt`) is subadditive. -/
theorem bwt_add_le (a b : BaseGroup → ZMod 2) : bwt (a + b) ≤ bwt a + bwt b := by
  unfold bwt
  have hsub : (Finset.univ.filter (fun h => (a + b) h = 1)) ⊆
      (Finset.univ.filter (fun h => a h = 1)) ∪ (Finset.univ.filter (fun h => b h = 1)) := by
    intro h hh
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply] at hh
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    have key : ∀ x y : ZMod 2, x + y = 1 → x = 1 ∨ y = 1 := by decide
    exact key (a h) (b h) hh
  exact le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)

/-- A single hexagon A-block has weight exactly 3. -/
theorem bwt_baseA_single : ∀ g : BaseGroup, bwt (baseA ⋆ Pi.single g 1) = 3 := by
  have key : ∀ g : BaseGroup, bwt (fun h => baseA (h - g)) = 3 := by decide +kernel
  intro g
  rw [conv_single_right]
  exact key g
/-- A single hexagon B-block has weight exactly 3. -/
theorem bwt_baseB_single : ∀ g : BaseGroup, bwt (baseB ⋆ Pi.single g 1) = 3 := by
  have key : ∀ g : BaseGroup, bwt (fun h => baseB (h - g)) = 3 := by decide +kernel
  intro g
  rw [conv_single_right]
  exact key g

/-- `∂₂` block values (definitional). -/
theorem bb2_zero (z : BaseGroup → ZMod 2) (h : BaseGroup) :
    bbBoundary2Fn baseA baseB z (h, 0) = (baseA ⋆ z) h := rfl
theorem bb2_one (z : BaseGroup → ZMod 2) (h : BaseGroup) :
    bbBoundary2Fn baseA baseB z (h, 1) = (baseB ⋆ z) h := rfl

/-- The B-block weight is at most the full boundary weight (`h ↦ (h,1)` injection). -/
theorem bwt_baseB_le_boundary (f : BaseGroup → ZMod 2) :
    bwt (baseB ⋆ f) ≤ (Finset.univ.filter (fun j : BaseGroup × Fin 2 =>
      bbBoundary2Fn baseA baseB f j ≠ 0)).card := by
  unfold bwt
  apply Finset.card_le_card_of_injOn (fun h => (h, (1 : Fin 2)))
  · intro h hh
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hh ⊢
    show bbBoundary2Fn baseA baseB f (h, 1) ≠ 0
    rw [bb2_one, hh]; exact one_ne_zero
  · intro a _ b _ hab; exact congrArg Prod.fst hab

/-- **Endgame transfer (hexagon)**: if the A-block of `∂₂f` is `A·δ_g` and `|∂₂f| ≤ 10`,
then `∂₂f = ∂₂δ_g`. -/
theorem transfer_hexagon (f : BaseGroup → ZMod 2) (g : BaseGroup)
    (hA : baseA ⋆ f = baseA ⋆ Pi.single g 1)
    (hwt : (Finset.univ.filter (fun j : BaseGroup × Fin 2 =>
      bbBoundary2Fn baseA baseB f j ≠ 0)).card ≤ 10) :
    bbBoundary2Fn baseA baseB f = bbBoundary2Fn baseA baseB (Pi.single g 1) := by
  set δ : BaseGroup → ZMod 2 := Pi.single g 1 with hδ
  have hself : ∀ x : ZMod 2, x + x = 0 := by decide
  have hAw : baseA ⋆ (f + δ) = 0 := by
    rw [conv_add_right, hA]; funext h; rw [Pi.add_apply]; exact hself _
  have hbound : bwt (baseB ⋆ (f + δ)) < 16 := by
    rw [conv_add_right]
    calc bwt (baseB ⋆ f + baseB ⋆ δ)
          ≤ bwt (baseB ⋆ f) + bwt (baseB ⋆ δ) := bwt_add_le _ _
      _ ≤ 10 + 3 := by
          gcongr
          · exact le_trans (bwt_baseB_le_boundary f) hwt
          · rw [hδ, bwt_baseB_single g]
      _ < 16 := by norm_num
  have hBw : baseB ⋆ (f + δ) = 0 := oneBlock_contra _ hAw hbound
  have hBeq : baseB ⋆ f = baseB ⋆ δ := by
    funext h
    have hpt : (baseB ⋆ f) h + (baseB ⋆ δ) h = 0 := by
      have := congrFun hBw h; rwa [conv_add_right, Pi.add_apply] at this
    have key : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
    exact key _ _ hpt
  funext ⟨h, j⟩
  show (if j = 0 then (baseA ⋆ f) h else (baseB ⋆ f) h)
      = (if j = 0 then (baseA ⋆ δ) h else (baseB ⋆ δ) h)
  by_cases hj : j = 0
  · rw [if_pos hj, if_pos hj]; exact congrFun hA h
  · rw [if_neg hj, if_neg hj]; exact congrFun hBeq h

/-- Block-weight decomposition (≤): the two blocks' weights sum to at most `|∂₂f|`
(disjoint `h↦(h,0)` / `h↦(h,1)` injections into the boundary support). -/
theorem bwt_blocks_le_boundary (f : BaseGroup → ZMod 2) :
    bwt (baseA ⋆ f) + bwt (baseB ⋆ f) ≤
    (Finset.univ.filter (fun j : BaseGroup × Fin 2 => bbBoundary2Fn baseA baseB f j ≠ 0)).card := by
  unfold bwt
  have injA : Function.Injective (fun h : BaseGroup => (h, (0 : Fin 2))) :=
    fun a b h => (Prod.mk.injEq ..).mp h |>.1
  have injB : Function.Injective (fun h : BaseGroup => (h, (1 : Fin 2))) :=
    fun a b h => (Prod.mk.injEq ..).mp h |>.1
  rw [← Finset.card_image_of_injective _ injA, ← Finset.card_image_of_injective _ injB,
    ← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    intro p hp
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hp with ⟨h, hh, rfl⟩ | ⟨h, hh, rfl⟩
    · rw [bb2_zero, hh]; exact one_ne_zero
    · rw [bb2_one, hh]; exact one_ne_zero
  · rw [Finset.disjoint_left]
    intro p hpa hpb
    simp only [Finset.mem_image, Finset.mem_filter] at hpa hpb
    obtain ⟨a, _, rfl⟩ := hpa
    obtain ⟨b, _, hb⟩ := hpb
    exact absurd ((Prod.mk.injEq ..).mp hb).2 (by decide)

/-- D-pair A-block is nonzero (weight ≥ 1): the probe cell `g + (3,0)` — or
`g + (0,1)` for the two directions `(3,4)`, `(3,5)`, whose second hexagon covers
`g + (3,0)` — carries value 1 (kernel `decide`, 12 × 36 single-cell checks). -/
theorem bwt_baseA_dpair_ge1 : ∀ g : BaseGroup, ∀ d ∈ pairDirections,
    1 ≤ bwt (baseA ⋆ (Pi.single g 1 + Pi.single (g + d) 1)) := by
  have key : ∀ d ∈ pairDirections, ∀ g : BaseGroup,
      ((fun h => baseA (h - g)) + fun h => baseA (h - (g + d)))
        (g + (if d = (3, 4) ∨ d = (3, 5) then (0, 1) else (3, 0))) = 1 := by
    decide +kernel
  intro g d hd
  rw [conv_add_right, conv_single_right, conv_single_right]
  unfold bwt
  exact Finset.one_le_card.mpr
    ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, key d hd g⟩⟩
/-- D-pair B-block has weight ≤ 6 (subadditivity + two weight-3 hexagons). -/
theorem bwt_baseB_dpair_le6 : ∀ g : BaseGroup, ∀ d ∈ pairDirections,
    bwt (baseB ⋆ (Pi.single g 1 + Pi.single (g + d) 1)) ≤ 6 := by
  intro g d _
  rw [conv_add_right]
  calc bwt (baseB ⋆ Pi.single g 1 + baseB ⋆ Pi.single (g + d) 1)
      ≤ bwt (baseB ⋆ Pi.single g 1) + bwt (baseB ⋆ Pi.single (g + d) 1) :=
        bwt_add_le _ _
    _ = 3 + 3 := by rw [bwt_baseB_single g, bwt_baseB_single (g + d)]
    _ ≤ 6 := by norm_num

/-- **Endgame transfer (D-pair)**: if the A-block of `∂₂f` is `A·(δ_g+δ_{g+d})`,
`d ∈ pairDirections`, and `|∂₂f| ≤ 10`, then `∂₂f = ∂₂(δ_g+δ_{g+d})`.  The crude
`10+6` bound only gives `≤16`; the block decomposition tightens `|B·f| ≤ 10−w_A ≤ 9`
(`w_A = bwt(A·witness) ≥ 1`), so `|B·w| ≤ 15 < 16`. -/
theorem transfer_dpair (f : BaseGroup → ZMod 2) (g d : BaseGroup) (hd : d ∈ pairDirections)
    (hA : baseA ⋆ f = baseA ⋆ (Pi.single g 1 + Pi.single (g + d) 1))
    (hwt : (Finset.univ.filter (fun j : BaseGroup × Fin 2 =>
      bbBoundary2Fn baseA baseB f j ≠ 0)).card ≤ 10) :
    bbBoundary2Fn baseA baseB f
      = bbBoundary2Fn baseA baseB (Pi.single g 1 + Pi.single (g + d) 1) := by
  set wit : BaseGroup → ZMod 2 := Pi.single g 1 + Pi.single (g + d) 1 with hwit
  have hself : ∀ x : ZMod 2, x + x = 0 := by decide
  have hAw : baseA ⋆ (f + wit) = 0 := by
    rw [conv_add_right, hA]; funext h; rw [Pi.add_apply]; exact hself _
  have hbound : bwt (baseB ⋆ (f + wit)) < 16 := by
    rw [conv_add_right]
    have hBf : bwt (baseB ⋆ f) ≤ 9 := by
      have hdec := bwt_blocks_le_boundary f
      have hA1 : 1 ≤ bwt (baseA ⋆ f) := by rw [hA]; exact bwt_baseA_dpair_ge1 g d hd
      omega
    have hBwit : bwt (baseB ⋆ wit) ≤ 6 := bwt_baseB_dpair_le6 g d hd
    calc bwt (baseB ⋆ f + baseB ⋆ wit)
          ≤ bwt (baseB ⋆ f) + bwt (baseB ⋆ wit) := bwt_add_le _ _
      _ ≤ 9 + 6 := add_le_add hBf hBwit
      _ < 16 := by norm_num
  have hBw : baseB ⋆ (f + wit) = 0 := oneBlock_contra _ hAw hbound
  have hBeq : baseB ⋆ f = baseB ⋆ wit := by
    funext h
    have hpt : (baseB ⋆ f) h + (baseB ⋆ wit) h = 0 := by
      have := congrFun hBw h; rwa [conv_add_right, Pi.add_apply] at this
    have key : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
    exact key _ _ hpt
  funext ⟨h, j⟩
  show (if j = 0 then (baseA ⋆ f) h else (baseB ⋆ f) h)
      = (if j = 0 then (baseA ⋆ wit) h else (baseB ⋆ wit) h)
  by_cases hj : j = 0
  · rw [if_pos hj, if_pos hj]; exact congrFun hA h
  · rw [if_neg hj, if_neg hj]; exact congrFun hBeq h

end LightStab
end BB
end Homological
end Stabilizer
end Quantum
