/-
# CRT layer frame for the base bb72 complex (A4 §3) — M1 + M3 foundation

Computable F₄, the group algebra `F₄[Z₂²]`, the CRT layer/torus coordinates on
`Z₆`, the six radical multipliers `Â_j`/`B̂_j`, and the **engine support-shape
lemma** over the 256-element ring.  Everything is built on explicit `Fin 4`
tables and `List.foldl` — NO `GaloisField`/`Finsupp`, which are noncomputable and
would defeat `decide` (the Phase-5 noncomputable-whnf hazard).

Promoted verbatim from the GREEN phase-6 probes `FrameProbe.lean` /
`EngineProbe.lean`; see those for the de-risking history (EngineProbe refuted the
feared "irreducibly symbolic radical-ideal algebra": the ≥3-layer dichotomy is a
finite kernel check).

**CONVENTIONS (A4 §3).** `ω = 2`, `ω² = 3` in the `Fin 4` model;
`Z₆ = Z₂ × Z₃` via `a ↦ (a mod 2, a mod 3)` (`s_x = x³`, `t_x = x⁴`); layers
indexed by `Z₂²` in the order `(0,0),(1,0),(0,1),(1,1) = 1, s_x, s_y, s_xs_y`.

**NOT YET HERE (M2 milestone):** the component transforms `V_j` and the
multiplicativity identity `V_j(A·z) = Â_j·ẑ_j` (needs the F₂-linearity bridge
lemma and carries the repo-left=lab-right / `ω` vs `ω²` convention risk).  This
file is the M1 (F₄ + ring) + M3 (engine) foundation those build on.
-/
import QEC.Stabilizer.Codes.BivariateBicycle.Gross.Defs

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BB
namespace CRTFrame

/-! ## §1 Computable F₄ as `Fin 4`: `(0, 1, ω, ω²) ↦ (0, 1, 2, 3)`.

Characteristic-2 addition table and the F₄ multiplication table. -/

/-- F₄ addition (characteristic 2): bitwise XOR on the `Fin 4` encoding (the table
`![![0,1,2,3], ![1,0,3,2], ![2,3,0,1], ![3,2,1,0]]`).  `Nat.xor` is
kernel-accelerated, which keeps the big `decide` walks downstream cheap. -/
def fadd : Fin 4 → Fin 4 → Fin 4 :=
  fun a b => ⟨(a.val ^^^ b.val) % 4, by omega⟩

/-- F₄ multiplication: the table `![![0,0,0,0], ![0,1,2,3], ![0,2,3,1], ![0,3,1,2]]`
packed row-major (`a*4 + b`) at 2 bits per entry into the literal `0x9c78e400`.
`Nat.shiftRight`/`Nat.mod` are kernel-accelerated (cf. `fadd`). -/
def fmul : Fin 4 → Fin 4 → Fin 4 :=
  fun a b => ⟨(0x9c78e400 >>> (2 * (a.val * 4 + b.val))) % 4, by omega⟩

/-- `ω^k` for `k ∈ Z₃`: `1, ω, ω²` ↦ `1, 2, 3`. -/
def omegaPow (k : ZMod 3) : Fin 4 := if k = 0 then 1 else if k = 1 then 2 else 3

/-! ### F₄ field axioms (all closed `∀` statements over the 4-element carrier,
discharged by `decide`). -/

theorem fadd_comm : ∀ a b : Fin 4, fadd a b = fadd b a := by decide
theorem fadd_assoc : ∀ a b c : Fin 4, fadd (fadd a b) c = fadd a (fadd b c) := by decide
theorem fadd_zero : ∀ a : Fin 4, fadd a 0 = a := by decide
theorem fadd_self : ∀ a : Fin 4, fadd a a = 0 := by decide
theorem fmul_comm : ∀ a b : Fin 4, fmul a b = fmul b a := by decide
theorem fmul_assoc : ∀ a b c : Fin 4, fmul (fmul a b) c = fmul a (fmul b c) := by decide
theorem fmul_one : ∀ a : Fin 4, fmul a 1 = a := by decide
theorem fmul_zero : ∀ a : Fin 4, fmul a 0 = 0 := by decide
theorem fmul_fadd : ∀ a b c : Fin 4, fmul a (fadd b c) = fadd (fmul a b) (fmul a c) := by decide
/-- F₄ is a field: every nonzero element has a multiplicative inverse. -/
theorem fmul_inv : ∀ a : Fin 4, a ≠ 0 → ∃ b, fmul a b = 1 := by decide

/-! ## §2 The group algebra `F₄[Z₂²] = (Z₂² → Fin 4)`: 16-element carrier,
256-element ring. -/

/-- Carrier of `F₄[Z₂²]`. -/
abbrev Ring := ZMod 2 × ZMod 2 → Fin 4

/-- The four layers in canonical order `(1, s_x, s_y, s_xs_y)`. -/
def allS : List (ZMod 2 × ZMod 2) := [((0 : ZMod 2), (0 : ZMod 2)), (1, 0), (0, 1), (1, 1)]

/-- Convolution product in `F₄[Z₂²]`. -/
def rmul (p q : Ring) : Ring :=
  fun s => allS.foldl (fun acc s' => fadd acc (fmul (p s') (q (s - s')))) 0

/-- The all-ones socle element `uv = 1 + s_x + s_y + s_xs_y`. -/
def uv : Ring := fun _ => 1

/-- Explicit ring element from its four layer values (canonical layer order
`1, s_x, s_y, s_xs_y`).  Together with `ring_eq_mkRing` this converts
`∀ r : Ring, …` sweeps into `∀ a b c d : Fin 4, …` sweeps — the form the
kernel can enumerate without whnf-ing the 256-element pi-type `Fintype`. -/
def mkRing (a b c d : Fin 4) : Ring := fun s =>
  if s = (0, 0) then a else if s = (1, 0) then b else if s = (0, 1) then c else d

/-- Every ring element is the `mkRing` of its four layer values. -/
theorem ring_eq_mkRing (r : Ring) :
    r = mkRing (r (0, 0)) (r (1, 0)) (r (0, 1)) (r (1, 1)) := by
  have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  funext s
  obtain ⟨s1, s2⟩ := s
  rcases h2 s1 with rfl | rfl <;> rcases h2 s2 with rfl | rfl <;> rfl

/-! ## §3 CRT coordinates on `Z₆`: layer (mod 2) and torus (mod 3). -/

/-- Layer coordinate of `a ∈ Z₆` (reduce mod 2). -/
def layer1 (a : ZMod 6) : ZMod 2 := (a.val : ZMod 2)

/-- Torus coordinate of `a ∈ Z₆` (reduce mod 3). -/
def torus1 (a : ZMod 6) : ZMod 3 := (a.val : ZMod 3)

/-- Layer `s ∈ Z₂²` of a base cell. -/
def layer (g : BaseGroup) : ZMod 2 × ZMod 2 := (layer1 g.1, layer1 g.2)

/-- Torus `t ∈ Z₃²` of a base cell. -/
def torus (g : BaseGroup) : ZMod 3 × ZMod 3 := (torus1 g.1, torus1 g.2)

/-! ## §4 The radical multipliers (A4 §3 table), as value vectors over the
layers `(0,0),(1,0),(0,1),(1,1) = (1, s_x, s_y, s_xs_y)`.

The six radical multipliers `Â₁, Â₃, Â₄, B̂₂, B̂₃, B̂₄` collapse to three distinct
value vectors, each with exactly one zero layer and three distinct nonzero
values — the input to the engine's ≥3-layer dichotomy. -/

/-- `Â₁ = Â₃ = u + ωv`, value vector `(3, 1, 2, 0)`. -/
def Ahat1 : Ring := fun s =>
  if s = (0, 0) then 3 else if s = (1, 0) then 1 else if s = (0, 1) then 2 else 0

/-- `Â₄ = u + ω²v`, value vector `(2, 1, 3, 0)`. -/
def Ahat4 : Ring := fun s =>
  if s = (0, 0) then 2 else if s = (1, 0) then 1 else if s = (0, 1) then 3 else 0

/-- `B̂₂ = B̂₃ = B̂₄ = ωu + v`, value vector `(3, 2, 1, 0)`. -/
def Bhat2 : Ring := fun s =>
  if s = (0, 0) then 3 else if s = (1, 0) then 2 else if s = (0, 1) then 1 else 0

/-! ## §5 Engine support-shape lemma (A4 §3).

For a radical multiplier `D` (here `Â₁`, `Â₄`, `B̂₂` — the three distinct
vectors): `D² = 0`, `Ann(D) = (D) = {αD + β·uv}` (a 2-dimensional ideal), and
every NONZERO ideal element has `≥ 3` nonzero layers.  All three are finite
checks over the 256-element ring (EngineProbe GREEN). -/

/-- The four F₄ values. -/
def f4list : List (Fin 4) := [0, 1, 2, 3]

/-- All 256 ring elements as an explicit list (4 layers × 4 values). -/
def allRing : List Ring :=
  f4list.flatMap fun a => f4list.flatMap fun b =>
    f4list.flatMap fun c => f4list.map fun d =>
      (fun s => if s = (0, 0) then a else if s = (1, 0) then b
                else if s = (0, 1) then c else d)

/-- All 16 F₄-pairs `(α, β)` generating the ideal `{αD + β·uv}`. -/
def all16 : List (Fin 4 × Fin 4) :=
  f4list.flatMap fun a => f4list.map fun b => (a, b)

/-- Number of nonzero layers of a ring element. -/
def nLayers (p : Ring) : Nat := (allS.filter (fun s => decide (p s ≠ 0))).length

/-- `r` agrees as a function with some `αD + β·uv`. -/
def inIdeal (D : Ring) (r : Ring) : Bool :=
  all16.any fun ab => allS.all fun s => decide (r s = fadd (fmul ab.1 (D s)) (fmul ab.2 (uv s)))

/-- `r` is annihilated by `D`: `r ⋆ D = 0`. -/
def annihilatedBy (D : Ring) (r : Ring) : Bool :=
  allS.all fun s => decide (rmul r D s = 0)

/-! ### Engine (D² = 0) for the three radical multipliers. -/

theorem Ahat1_sq : rmul Ahat1 Ahat1 = (fun _ => 0) := by decide +kernel
theorem Ahat4_sq : rmul Ahat4 Ahat4 = (fun _ => 0) := by decide +kernel
theorem Bhat2_sq : rmul Bhat2 Bhat2 = (fun _ => 0) := by decide +kernel

/-! ### Engine (i): `Ann(D) = (D)`.  The 256-element annihilator set equals the
16-element ideal `{αD + β·uv}`. -/

theorem Ahat1_ann_eq_ideal :
    allRing.all (fun r => annihilatedBy Ahat1 r == inIdeal Ahat1 r) = true := by decide +kernel
theorem Ahat4_ann_eq_ideal :
    allRing.all (fun r => annihilatedBy Ahat4 r == inIdeal Ahat4 r) = true := by decide +kernel
theorem Bhat2_ann_eq_ideal :
    allRing.all (fun r => annihilatedBy Bhat2 r == inIdeal Bhat2 r) = true := by decide +kernel

/-! ### Engine (ii): every NONZERO ideal element has `≥ 3` nonzero layers.
This is the exact L4b "Floor" input. -/

theorem Ahat1_ideal_ge3 : all16.all (fun ab =>
    let r : Ring := fun s => fadd (fmul ab.1 (Ahat1 s)) (fmul ab.2 (uv s))
    decide (r = (fun _ => 0)) || decide (nLayers r ≥ 3)) = true := by decide +kernel
theorem Ahat4_ideal_ge3 : all16.all (fun ab =>
    let r : Ring := fun s => fadd (fmul ab.1 (Ahat4 s)) (fmul ab.2 (uv s))
    decide (r = (fun _ => 0)) || decide (nLayers r ≥ 3)) = true := by decide +kernel
theorem Bhat2_ideal_ge3 : all16.all (fun ab =>
    let r : Ring := fun s => fadd (fmul ab.1 (Bhat2 s)) (fmul ab.2 (uv s))
    decide (r = (fun _ => 0)) || decide (nLayers r ≥ 3)) = true := by decide +kernel

/-! ## §6 The component transform `V` and its F₂-linearity (M2 bridge).

`V psi s f = Σ_{h : layer h = s, f h = 1} psi h` (sum in F₄).  The load-bearing
fact for the multiplicativity engine is that `V` is **F₂-linear in the chain**
`f` (`V_add`), proved from a generic char-2 fold-splitting lemma (`foldl_char2`,
whose only arithmetic content is one `decide` over the 256 `Bool²×Fin 4³`
accumulator cases).  This is what lifts the basis-chain multiplicativity
(M2-(A): `V_j(baseP⋆δ_p) = P̂_j·V_j(δ_p)`, a kernel `decide` over the 36 `δ_p`, all
10 (j,P) instances GREEN in `phase6/MultProbe.lean`) to all chains `z`.  The five
component characters are the A4 §3 frame characters. -/

/-- Enumeration of the base group (36 cells). -/
def allG : List BaseGroup :=
  (List.range 6).flatMap (fun a => (List.range 6).map (fun b => ((a : ZMod 6), (b : ZMod 6))))

/-- Component characters (A4 §3): ψ₀=1, ψ₁=ω^{t_y}, ψ₂=ω^{t_x},
ψ₃=ω^{t_x+t_y}, ψ₄=ω^{t_x+2t_y}. -/
def psi0 : BaseGroup → Fin 4 := fun _ => 1
def psi1 : BaseGroup → Fin 4 := fun g => omegaPow (torus1 g.2)
def psi2 : BaseGroup → Fin 4 := fun g => omegaPow (torus1 g.1)
def psi3 : BaseGroup → Fin 4 := fun g => omegaPow (torus1 g.1 + torus1 g.2)
def psi4 : BaseGroup → Fin 4 := fun g => omegaPow (torus1 g.1 + 2 * torus1 g.2)

/-- Generic char-2 transform: `fadd`-fold of `b` over the cells where `P` holds. -/
def fsum (b : BaseGroup → Fin 4) (P : BaseGroup → Bool) : Fin 4 :=
  allG.foldl (fun acc h => if P h then fadd acc (b h) else acc) 0

/-- **The char-2 fold splits over an XOR predicate** (generic over any list /
predicates; the Fin-4 accumulator step is one `decide` over all 256
`Bool²×Fin 4³` cases). -/
theorem foldl_char2 (b : BaseGroup → Fin 4) (Pf Pg : BaseGroup → Bool) :
    ∀ (L : List BaseGroup) (aF aG : Fin 4),
      fadd (L.foldl (fun acc h => if Pf h then fadd acc (b h) else acc) aF)
           (L.foldl (fun acc h => if Pg h then fadd acc (b h) else acc) aG)
      = L.foldl (fun acc h => if (Pf h != Pg h) then fadd acc (b h) else acc)
          (fadd aF aG) := by
  have accStep : ∀ (p q : Bool) (x y z : Fin 4),
      fadd (if p then fadd x z else x) (if q then fadd y z else y)
        = if (p != q) then fadd (fadd x y) z else fadd x y := by decide
  intro L
  induction L with
  | nil => intro aF aG; rfl
  | cons h t ih =>
    intro aF aG
    simp only [List.foldl_cons]
    rw [ih, accStep (Pf h) (Pg h) aF aG (b h)]

/-- `fsum` is F₂-additive on predicates: XOR of predicates adds the sums. -/
theorem fsum_xor (b : BaseGroup → Fin 4) (Pf Pg : BaseGroup → Bool) :
    fadd (fsum b Pf) (fsum b Pg) = fsum b (fun h => Pf h != Pg h) := by
  have h := foldl_char2 b Pf Pg allG 0 0
  simpa [fsum] using h

/-- The CRT component transform at layer `s`:
`V psi s f = Σ_{h : layer h = s, f h = 1} psi h` (sum in F₄). -/
def V (psi : BaseGroup → Fin 4) (s : ZMod 2 × ZMod 2) (f : BaseGroup → ZMod 2) : Fin 4 :=
  fsum psi (fun h => decide (layer h = s) && decide (f h = 1))

/-- **The F₂-linearity bridge (M2-(B)): `V` is additive in the chain.**  This is
the load-bearing step that lifts the basis-chain multiplicativity (M2-(A),
a kernel `decide` over the 36 `δ_p`) to all chains `z`; it is the piece with no
mathlib analogue (F₄ is `Fin 4`+tables, so there is no `AddCommMonoid` to borrow
`Finset.sum` additivity from — hence the hand-rolled char-2 `foldl_char2`). -/
theorem V_add (psi : BaseGroup → Fin 4) (s : ZMod 2 × ZMod 2)
    (f g : BaseGroup → ZMod 2) :
    V psi s (f + g) = fadd (V psi s f) (V psi s g) := by
  have hz : ∀ a b : ZMod 2, decide (a + b = 1) = (decide (a = 1) != decide (b = 1)) := by decide
  have hb : ∀ L F G : Bool, (L && (F != G)) = ((L && F) != (L && G)) := by decide
  unfold V
  rw [fsum_xor]
  congr 1
  funext h
  rw [Pi.add_apply, hz, hb]

/-! ## §7 General multiplicativity `V_j(baseP⋆z) = P̂_j·V_j(z)` for all chains.

The basis-chain identity (M2-(A): `V_j(baseP⋆δ_p) = P̂_j·V_j(δ_p)`, kernel `decide`
on the `Pi.single p 1`, all 10 (j,P) instances GREEN in `phase6/MultProbe.lean`)
lifts to **all** chains `z` because every map in sight is F₂-linear: the
convolution `conv baseP ·` (`conv_add_right`), the transform `V` (`V_add`), and
the ring product `rmul` (`rmul_add_right`).  `mult_of_basis` packages the support
induction; the six radical-multiplier instances the engine (§5) consumes are
spelled out below. -/

/-- Generic F₄ fold-additivity: a `fadd`-fold of a pointwise sum splits. -/
theorem foldl_add {α : Type} (m n : α → Fin 4) :
    ∀ (L : List α) (aM aN : Fin 4),
      L.foldl (fun acc s' => fadd acc (fadd (m s') (n s'))) (fadd aM aN)
        = fadd (L.foldl (fun acc s' => fadd acc (m s')) aM)
               (L.foldl (fun acc s' => fadd acc (n s')) aN) := by
  have step : ∀ (w x y z : Fin 4),
      fadd (fadd w x) (fadd y z) = fadd (fadd w y) (fadd x z) := by decide
  intro L
  induction L with
  | nil => intro aM aN; rfl
  | cons h t ih =>
    intro aM aN
    simp only [List.foldl_cons]
    rw [step aM aN (m h) (n h)]
    exact ih (fadd aM (m h)) (fadd aN (n h))

/-- `rmul` is additive in its second argument. -/
theorem rmul_add_right (P q q' : ZMod 2 × ZMod 2 → Fin 4) :
    rmul P (fun t => fadd (q t) (q' t)) = fun s => fadd (rmul P q s) (rmul P q' s) := by
  funext s
  unfold rmul
  simp only [fmul_fadd]
  exact foldl_add (fun s' => fmul (P s') (q (s - s')))
    (fun s' => fmul (P s') (q' (s - s'))) allS 0 0

/-- `V` of the zero chain is `0`. -/
theorem V_zero (psi : BaseGroup → Fin 4) (s : ZMod 2 × ZMod 2) :
    V psi s (0 : BaseGroup → ZMod 2) = 0 := by
  unfold V fsum
  have : (fun h => decide (layer h = s) && decide ((0 : BaseGroup → ZMod 2) h = 1))
      = (fun _ : BaseGroup => false) := by funext h; simp
  rw [this]
  induction allG with
  | nil => rfl
  | cons a t ih => simp only [Bool.false_eq_true, if_false]; exact ih

/-- `rmul P 0 = 0`. -/
theorem rmul_zero_right (P : ZMod 2 × ZMod 2 → Fin 4) :
    rmul P (fun _ => 0) = fun _ => 0 := by
  funext s
  unfold rmul
  have hmul : ∀ x : Fin 4, fmul x 0 = 0 := by decide
  simp only [hmul]
  induction allS with
  | nil => rfl
  | cons a t ih => simpa [fadd_zero] using ih

/-- Indicator of a finset as a `ZMod 2` chain. -/
def ind (S : Finset BaseGroup) : BaseGroup → ZMod 2 := fun g => if g ∈ S then 1 else 0

theorem ind_empty : ind ∅ = 0 := by funext g; simp [ind]

theorem ind_insert {p : BaseGroup} {S : Finset BaseGroup} (hp : p ∉ S) :
    ind (insert p S) = Pi.single p 1 + ind S := by
  funext g
  simp only [ind, Finset.mem_insert, Pi.add_apply, Pi.single_apply]
  by_cases hgp : g = p
  · have hgS : g ∉ S := by rw [hgp]; exact hp
    rw [if_pos (Or.inl hgp), if_pos hgp, if_neg hgS, add_zero]
  · by_cases hgS : g ∈ S
    · rw [if_pos (Or.inr hgS), if_neg hgp, if_pos hgS, zero_add]
    · rw [if_neg (not_or.mpr ⟨hgp, hgS⟩), if_neg hgp, if_neg hgS, add_zero]

theorem self_eq_ind_filter (z : BaseGroup → ZMod 2) :
    z = ind (Finset.univ.filter (fun p => z p = 1)) := by
  have hz : ∀ a : ZMod 2, (if a = 1 then (1 : ZMod 2) else 0) = a := by decide
  funext g
  simp only [ind, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (hz (z g)).symm

/-- **General multiplicativity from the basis case.**  If the multiplicativity
identity holds on every point-mass chain `Pi.single p 1`, it holds for every
chain `z` — by F₂-linearity of `conv baseP ·`, `V`, and `rmul`. -/
theorem mult_of_basis (psi : BaseGroup → Fin 4) (P : BaseGroup → ZMod 2)
    (Phat : ZMod 2 × ZMod 2 → Fin 4)
    (hbasis : ∀ (p : BaseGroup) (s : ZMod 2 × ZMod 2),
      V psi s (P ⋆ Pi.single p 1) = rmul Phat (fun s' => V psi s' (Pi.single p 1)) s)
    (z : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) :
    V psi s (P ⋆ z) = rmul Phat (fun s' => V psi s' z) s := by
  have goal_add : ∀ (a b : BaseGroup → ZMod 2),
      (∀ s, V psi s (P ⋆ a) = rmul Phat (fun s' => V psi s' a) s) →
      (∀ s, V psi s (P ⋆ b) = rmul Phat (fun s' => V psi s' b) s) →
      (∀ s, V psi s (P ⋆ (a + b)) = rmul Phat (fun s' => V psi s' (a + b)) s) := by
    intro a b ha hb s
    rw [conv_add_right, V_add]
    rw [show (fun s' => V psi s' (a + b))
        = (fun s' => fadd (V psi s' a) (V psi s' b)) from by funext s'; rw [V_add]]
    rw [rmul_add_right, ha s, hb s]
  have goal_zero : ∀ s, V psi s (P ⋆ (0 : BaseGroup → ZMod 2))
      = rmul Phat (fun s' => V psi s' (0 : BaseGroup → ZMod 2)) s := by
    intro s
    have hc0 : P ⋆ (0 : BaseGroup → ZMod 2) = 0 := by funext g; simp [conv_apply]
    rw [hc0, V_zero,
      show (fun s' => V psi s' (0 : BaseGroup → ZMod 2)) = (fun _ => 0) from by
        funext s'; exact V_zero psi s',
      rmul_zero_right]
  have key : ∀ (S : Finset BaseGroup) (s),
      V psi s (P ⋆ ind S) = rmul Phat (fun s' => V psi s' (ind S)) s := by
    intro S
    induction S using Finset.induction with
    | empty => rw [ind_empty]; exact goal_zero
    | @insert p S hp ih => rw [ind_insert hp]; exact goal_add _ _ (hbasis p) ih
  rw [self_eq_ind_filter z]
  exact key _ s

/-! ### The six radical-multiplier multiplicativity identities (engine inputs).
For each, a kernel `decide` discharges the 36-`δ_p` basis case (in the sparse
`conv P δ_p = P (· - p)` form supplied by `basis_of_translate`, so no
`Finset.sum` ever reaches the kernel); `mult_of_basis` lifts it to all `z`. -/

/-- Sparse form of right-convolution with a point mass:
`conv P δ_p = P (· - p)` (from `conv_comm` + `conv_single_left`). -/
theorem conv_single_right (P : BaseGroup → ZMod 2) (p : BaseGroup) :
    P ⋆ Pi.single p 1 = fun g => P (g - p) := by
  rw [conv_comm, conv_single_left]

/-- Reduce the `hbasis` obligation of `mult_of_basis` to its translate form
`V psi s (P (· - p)) = …`: a closed 144-case statement with no `Finset.sum`
under the binder, hence checkable by a plain kernel `decide` (the direct form
would force the kernel through 36 `Finset.univ` sums per case). -/
theorem basis_of_translate {psi : BaseGroup → Fin 4} {P : BaseGroup → ZMod 2}
    {Phat : Ring}
    (h : ∀ (p : BaseGroup) (s : ZMod 2 × ZMod 2),
      V psi s (fun g => P (g - p)) = rmul Phat (fun s' => V psi s' (Pi.single p 1)) s)
    (p : BaseGroup) (s : ZMod 2 × ZMod 2) :
    V psi s (P ⋆ Pi.single p 1) = rmul Phat (fun s' => V psi s' (Pi.single p 1)) s := by
  rw [conv_single_right]
  exact h p s

/-- `Â₁`: `V₁(A⋆z) = Â₁·V₁(z)`. -/
theorem mult_A1 (z : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) :
    V psi1 s (baseA ⋆ z) = rmul Ahat1 (fun s' => V psi1 s' z) s :=
  mult_of_basis psi1 baseA Ahat1 (basis_of_translate (by decide +kernel)) z s

/-- `Â₃ = Â₁`: `V₃(A⋆z) = Â₁·V₃(z)`. -/
theorem mult_A3 (z : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) :
    V psi3 s (baseA ⋆ z) = rmul Ahat1 (fun s' => V psi3 s' z) s :=
  mult_of_basis psi3 baseA Ahat1 (basis_of_translate (by decide +kernel)) z s

/-- `Â₄`: `V₄(A⋆z) = Â₄·V₄(z)`. -/
theorem mult_A4 (z : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) :
    V psi4 s (baseA ⋆ z) = rmul Ahat4 (fun s' => V psi4 s' z) s :=
  mult_of_basis psi4 baseA Ahat4 (basis_of_translate (by decide +kernel)) z s

/-- `B̂₂`: `V₂(B⋆z) = B̂₂·V₂(z)`. -/
theorem mult_B2 (z : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) :
    V psi2 s (baseB ⋆ z) = rmul Bhat2 (fun s' => V psi2 s' z) s :=
  mult_of_basis psi2 baseB Bhat2 (basis_of_translate (by decide +kernel)) z s

/-- `B̂₃ = B̂₂`: `V₃(B⋆z) = B̂₂·V₃(z)`. -/
theorem mult_B3 (z : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) :
    V psi3 s (baseB ⋆ z) = rmul Bhat2 (fun s' => V psi3 s' z) s :=
  mult_of_basis psi3 baseB Bhat2 (basis_of_translate (by decide +kernel)) z s

/-- `B̂₄ = B̂₂`: `V₄(B⋆z) = B̂₂·V₄(z)`. -/
theorem mult_B4 (z : BaseGroup → ZMod 2) (s : ZMod 2 × ZMod 2) :
    V psi4 s (baseB ⋆ z) = rmul Bhat2 (fun s' => V psi4 s' z) s :=
  mult_of_basis psi4 baseB Bhat2 (basis_of_translate (by decide +kernel)) z s

end CRTFrame
end BB
end Homological
end Stabilizer
end Quantum
