import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic
import QEC.Stabilizer.Foundations.BinarySymplectic.Core
import QEC.Stabilizer.Foundations.BinarySymplectic.SymplecticInner
import QEC.Stabilizer.Foundations.BinarySymplectic.CheckMatrix
import QEC.Stabilizer.Framework.Symplectic.SymplecticSpan
import QEC.Stabilizer.Framework.Symplectic.SymplecticOrthogonal
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerGroup
import QEC.Stabilizer.Framework.Core.Stabilizer.Centralizer
import QEC.Stabilizer.Framework.Core.Stabilizer.StabilizerCode
import QEC.Stabilizer.Framework.Core.Logical.LogicalOperators
import QEC.Stabilizer.Foundations.PauliGroup.NQubitElement

/-!
# Inner-centralizer classification (Milestone M4)

Milestone **M4** of the CSS concatenation plan
(`qec-lab:pipeline/attempts/concat_css_general/plan.md`) — the long pole of the distance
argument. For a `k = 1` stabilizer code, the centralizer of the stabilizer is
`stabilizer ⊔ ⟨X̄₁, Z̄₁⟩`; the distance proof needs to read off, per block, whether
a centralizing operator is "stabilizer-like" or a genuine logical.

This module assembles the `SymplecticSpan` bridge into two results:

- **`centralizer_classify_of_k1`** (the *weak dichotomy*, proven here) — every
  centralizing element either has its operator part realized by a stabilizer
  element, or is a nontrivial logical. This is the per-block split the distance
  argument applies to each `restrictBlock b L`.

  **Note on the statement.** The plan's draft phrased the "trivial" branch as
  `g ∈ stabilizer`. That over-claims: `g` may differ from a stabilizer element by
  a global phase (`i`, `-1`, `-i`), and such a phased element is neither in the
  stabilizer (no `-I`) nor a *nontrivial* logical (its operator part coincides
  with a stabilizer's). The phase-clean, downstream-usable form — and the one the
  repo's `no_weight_w_logical_of_centralizer_in_span` already uses — states the
  trivial branch in **operator-part** terms: `∃ s ∈ stabilizer, s.operators =
  g.operators`. That is exactly what the weight/distance argument consumes.

- **`operators_eq_stab_of_commutes_both_logicals`** (the *decisive direction* —
  still `sorry`) — a centralizing element that commutes with *both* inner
  logicals has its operator part realized by a stabilizer element. This is the
  genuine content of M4 and the one place the weak dichotomy is insufficient: it
  is the `k = 1` "dimension-2 quotient" fact `sympOrthogonal(span{stab rows,
  X̄, Z̄}) = span{stab rows}`. See its doc-comment for the precise scoped goal.
-/

namespace Quantum.StabilizerGroup

open NQubitPauliGroupElement

variable {n k : ℕ}

/-- **(M4, weak dichotomy.)** Any element of the centralizer of a stabilizer code's
stabilizer group is, in operator-part terms, either *stabilizer-like* (some stabilizer
element shares its operator part) or a *nontrivial logical*.

Proof: split on whether the symplectic vector of `g.operators` lies in the row span
`sympSpan C.generatorsList`. If it does, `exists_mem_closure_of_symp_in_span` realizes
the operator part by a closure (= stabilizer) element. If it does not, all three clauses
of `IsNontrivialLogicalOperator` hold — centralizer membership is the hypothesis, and the
"not a stabilizer / operator-part distinct from every stabilizer" clauses follow because
any stabilizer element's symplectic vector *does* lie in `sympSpan` (the generators are
phase-0, so `mem_closure_implies_symp_in_span` applies). No dimension count, no `k = 1`. -/
theorem centralizer_classify_of_k1 (C : StabilizerCode n k)
    (g : NQubitPauliGroupElement n) (hg : g ∈ centralizer C.toStabilizerGroup) :
    (∃ s ∈ C.toStabilizerGroup.toSubgroup, s.operators = g.operators) ∨
      IsNontrivialLogicalOperator g C.toStabilizerGroup := by
  classical
  by_cases hin : NQubitPauliOperator.toSymplectic g.operators ∈ sympSpan C.generatorsList
  · exact Or.inl (exists_mem_closure_of_symp_in_span C.generatorsList g.operators hin)
  · refine Or.inr ((IsNontrivialLogicalOperator_iff g C.toStabilizerGroup).mpr ⟨hg, ?_, ?_⟩)
    · intro hmem
      exact hin (mem_closure_implies_symp_in_span C.generatorsList C.generators_phaseZero g hmem)
    · intro s hs heq
      refine hin ?_
      have hs' := mem_closure_implies_symp_in_span C.generatorsList C.generators_phaseZero s hs
      rwa [heq] at hs'

/-! ## The symplectic form as a nondegenerate `BilinForm` (for the dimension count) -/

section BilinForm

open NQubitPauliOperator

/-- The two halves of `Fin (n + n)` are disjoint: an X-index never equals a Z-index. -/
private lemma castAdd_ne_natAdd (i k : Fin n) : Fin.castAdd n i ≠ Fin.natAdd n k := by
  intro h; have := Fin.ext_iff.mp h; simp [Fin.val_castAdd] at this; omega

/-- The symplectic bilinear form on `F₂^{2n}`, bundled as a mathlib `BilinForm`. -/
noncomputable def sympBilinForm (n : ℕ) :
    LinearMap.BilinForm (ZMod 2) (Fin (n + n) → ZMod 2) :=
  LinearMap.mk₂ (ZMod 2) symplecticBilinear
    symplecticBilinear_add_left
    (fun c v w => by rw [symplecticBilinear_smul_left, smul_eq_mul])
    symplecticBilinear_add_right
    (fun c v w => by rw [symplecticBilinear_smul_right, smul_eq_mul])

@[simp] lemma sympBilinForm_apply (v w : Fin (n + n) → ZMod 2) :
    sympBilinForm n v w = symplecticBilinear v w := rfl

/-- The symplectic form is symmetric (over `ZMod 2`, the cross terms coincide). -/
lemma symplecticBilinear_comm (v w : Fin (n + n) → ZMod 2) :
    symplecticBilinear v w = symplecticBilinear w v := by
  unfold symplecticBilinear
  exact Finset.sum_congr rfl (fun i _ => by ring)

lemma sympBilinForm_isRefl : (sympBilinForm (n := n)).IsRefl := by
  intro x y h
  rw [sympBilinForm_apply, symplecticBilinear_comm]
  rwa [sympBilinForm_apply] at h

/-- The symplectic form is nondegenerate: testing against the standard basis vectors
`Pi.single` recovers each coordinate. -/
lemma sympBilinForm_nondegenerate : (sympBilinForm (n := n)).Nondegenerate := by
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft sympBilinForm_isRefl).mpr ?_
  intro v hv
  funext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · -- X-index: test against `single (natAdd i) 1`, recovering `v (castAdd i)`.
    have key : symplecticBilinear v (Pi.single (Fin.natAdd n i) (1 : ZMod 2)) =
        v (Fin.castAdd n i) := by
      unfold symplecticBilinear
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, Pi.single_eq_of_ne (castAdd_ne_natAdd i i)]; ring
      · intro k _ hk
        rw [Pi.single_eq_of_ne (show Fin.natAdd n k ≠ Fin.natAdd n i by simp [hk]),
            Pi.single_eq_of_ne (castAdd_ne_natAdd k i)]; ring
      · intro h; exact absurd (Finset.mem_univ i) h
    have := hv (Pi.single (Fin.natAdd n i) (1 : ZMod 2))
    rw [sympBilinForm_apply, key] at this
    simpa using this
  · -- Z-index: test against `single (castAdd i) 1`, recovering `v (natAdd i)`.
    have key : symplecticBilinear v (Pi.single (Fin.castAdd n i) (1 : ZMod 2)) =
        v (Fin.natAdd n i) := by
      unfold symplecticBilinear
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm (castAdd_ne_natAdd i i))]; ring
      · intro k _ hk
        rw [Pi.single_eq_of_ne (Ne.symm (castAdd_ne_natAdd i k)),
            Pi.single_eq_of_ne (show Fin.castAdd n k ≠ Fin.castAdd n i by simp [hk])]; ring
      · intro h; exact absurd (Finset.mem_univ i) h
    have := hv (Pi.single (Fin.castAdd n i) (1 : ZMod 2))
    rw [sympBilinForm_apply, key] at this
    simpa using this

/-- Membership in the symplectic orthogonal of a span reduces to orthogonality against the
spanning set (the form is linear in the first argument). -/
lemma mem_sympBilinForm_orthogonal_span_iff (S : Set (Fin (n + n) → ZMod 2))
    (m : Fin (n + n) → ZMod 2) :
    m ∈ LinearMap.BilinForm.orthogonal (sympBilinForm n) (Submodule.span (ZMod 2) S) ↔
      ∀ s ∈ S, symplecticBilinear s m = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h s hs
    have := h s (Submodule.subset_span hs)
    rwa [LinearMap.BilinForm.isOrtho_def, sympBilinForm_apply] at this
  · intro h w hw
    rw [LinearMap.BilinForm.isOrtho_def, sympBilinForm_apply]
    induction hw using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero => simp [symplecticBilinear]
    | add x y _ _ hx hy => rw [symplecticBilinear_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [symplecticBilinear_smul_left, hx, mul_zero]

/-- The symplectic orthogonal sends `⊔` to `⊓`. -/
lemma sympBilinForm_orthogonal_sup (P Q : Submodule (ZMod 2) (Fin (n + n) → ZMod 2)) :
    LinearMap.BilinForm.orthogonal (sympBilinForm n) (P ⊔ Q) =
      LinearMap.BilinForm.orthogonal (sympBilinForm n) P ⊓
        LinearMap.BilinForm.orthogonal (sympBilinForm n) Q := by
  refine le_antisymm (le_inf (LinearMap.BilinForm.orthogonal_le le_sup_left)
    (LinearMap.BilinForm.orthogonal_le le_sup_right)) ?_
  intro m hm
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro w hw
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hw
  rw [LinearMap.BilinForm.isOrtho_def, map_add, LinearMap.add_apply,
    show (sympBilinForm n) p m = 0 from
      LinearMap.BilinForm.isOrtho_def.mp ((LinearMap.BilinForm.mem_orthogonal_iff.mp hm.1) p hp),
    show (sympBilinForm n) q m = 0 from
      LinearMap.BilinForm.isOrtho_def.mp ((LinearMap.BilinForm.mem_orthogonal_iff.mp hm.2) q hq),
    add_zero]

end BilinForm

section Kernel

open NQubitPauliOperator Module

/-- **(M4, decisive direction — the long pole.)** For a `k = 1` code with linearly-independent
check-matrix rows, a centralizing element that commutes with *both* inner logicals `X̄₁`, `Z̄₁`
has its operator part realized by a stabilizer element.

The proof reduces (via `exists_mem_closure_of_symp_in_span`) to the symplectic core
`toSymplectic g.operators ∈ sympSpan C.generatorsList`, the `k = 1` *dimension-2 quotient*
fact. Writing `V = sympSpan L` (row span), `U = span{X̄, Z̄}`, and `W = V ⊔ U`:
`g ∈ centralizer` and commuting with `X̄, Z̄` put `symp(g) ∈ Wᗮ`. The form is nondegenerate,
so `dim Wᗮ = 2n − dim W`. The rows are independent (`dim V = n − 1`); `X̄, Z̄` are independent
(anticommuting pair, `dim U = 2`) and meet `V` trivially (`X̄, Z̄ ⊥ V`), so `dim W = n + 1` and
`dim Wᗮ = n − 1 = dim V`. Since `V ⊆ Wᗮ` (the stabilizer is isotropic and commutes with the
logicals), `V = Wᗮ`, whence `symp(g) ∈ V`.

Row-independence (`rowsLinearIndependent`) is an explicit hypothesis: `StabilizerCode` carries
only the weaker subgroup `GeneratorsIndependent`. For a concrete code it is `native_decide`-able
(as the small CSS codes discharge `by decide`). -/
theorem operators_eq_stab_of_commutes_both_logicals (C : StabilizerCode n 1)
    (hindep : rowsLinearIndependent C.generatorsList)
    (g : NQubitPauliGroupElement n) (hg : g ∈ centralizer C.toStabilizerGroup)
    (hX : g * C.logicalX 0 = C.logicalX 0 * g)
    (hZ : g * C.logicalZ 0 = C.logicalZ 0 * g) :
    ∃ s ∈ C.toStabilizerGroup.toSubgroup, s.operators = g.operators := by
  classical
  apply exists_mem_closure_of_symp_in_span C.generatorsList g.operators
  have hn1 : 1 ≤ n := C.hk
  set xv := toSymplectic (C.logicalX 0).operators with hxv
  set zv := toSymplectic (C.logicalZ 0).operators with hzv
  set U : Submodule (ZMod 2) (Fin (n + n) → ZMod 2) := Submodule.span (ZMod 2) {xv, zv} with hU
  -- Pairing values of the symplectic form on the logicals.
  have hXZ : sympBilinForm n xv zv = 1 := by
    rw [hxv, hzv, sympBilinForm_apply, symplecticBilinear_toSymplectic]
    exact (anticommutes_iff_symplectic_inner_one _ _).mp (C.logicalOps 0).anticommute
  have hZX : sympBilinForm n zv xv = 1 := by
    rw [hxv, hzv, sympBilinForm_apply, symplecticBilinear_comm, symplecticBilinear_toSymplectic]
    exact (anticommutes_iff_symplectic_inner_one _ _).mp (C.logicalOps 0).anticommute
  have hXX : sympBilinForm n xv xv = 0 := by
    rw [hxv, sympBilinForm_apply, symplecticBilinear_toSymplectic]
    exact (commutes_iff_symplectic_inner_zero _ _).mp rfl
  have hZZ : sympBilinForm n zv zv = 0 := by
    rw [hzv, sympBilinForm_apply, symplecticBilinear_toSymplectic]
    exact (commutes_iff_symplectic_inner_zero _ _).mp rfl
  -- Any centralizing element is symplectically orthogonal to every generator row.
  have hcomm : ∀ p : NQubitPauliGroupElement n, p ∈ centralizer C.toStabilizerGroup →
      ∀ i : Fin C.generatorsList.length,
      symplecticBilinear (checkMatrix C.generatorsList i) (toSymplectic p.operators) = 0 := by
    intro p hp i
    rw [show checkMatrix C.generatorsList i
          = toSymplectic (C.generatorsList.get i).operators from by ext j; rfl,
        symplecticBilinear_toSymplectic]
    exact (commutes_iff_symplectic_inner_zero _ _).mp
      ((mem_centralizer_iff p C.toStabilizerGroup).mp hp (C.generatorsList.get i)
        (Subgroup.subset_closure (List.get_mem _ _)))
  -- The logicals lie in `Vᗮ` (they commute with every generator).
  have hxv_V : xv ∈ LinearMap.BilinForm.orthogonal (sympBilinForm n)
      (sympSpan C.generatorsList) := by
    rw [sympSpan, mem_sympBilinForm_orthogonal_span_iff]
    rintro _ ⟨i, rfl⟩; rw [hxv]; exact hcomm _ (C.logicalOps 0).x_mem_centralizer i
  have hzv_V : zv ∈ LinearMap.BilinForm.orthogonal (sympBilinForm n)
      (sympSpan C.generatorsList) := by
    rw [sympSpan, mem_sympBilinForm_orthogonal_span_iff]
    rintro _ ⟨i, rfl⟩; rw [hzv]; exact hcomm _ (C.logicalOps 0).z_mem_centralizer i
  -- `g ∈ Vᗮ` and `g ∈ Uᗮ`.
  have hgv_V : toSymplectic g.operators ∈ LinearMap.BilinForm.orthogonal (sympBilinForm n)
      (sympSpan C.generatorsList) := by
    rw [sympSpan, mem_sympBilinForm_orthogonal_span_iff]
    rintro _ ⟨i, rfl⟩; exact hcomm _ hg i
  have hgv_U : toSymplectic g.operators ∈ LinearMap.BilinForm.orthogonal (sympBilinForm n) U := by
    rw [hU, mem_sympBilinForm_orthogonal_span_iff]
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · rw [hxv, symplecticBilinear_toSymplectic]
      exact (commutes_iff_symplectic_inner_zero _ _).mp hX.symm
    · rw [hzv, symplecticBilinear_toSymplectic]
      exact (commutes_iff_symplectic_inner_zero _ _).mp hZ.symm
  -- `g ∈ Wᗮ`.
  have hgv_W : toSymplectic g.operators ∈ LinearMap.BilinForm.orthogonal (sympBilinForm n)
      (sympSpan C.generatorsList ⊔ U) := by
    rw [sympBilinForm_orthogonal_sup]; exact ⟨hgv_V, hgv_U⟩
  -- Dimensions.
  have hfinV : finrank (ZMod 2) (sympSpan C.generatorsList) = n - 1 := by
    have h := finrank_span_eq_card hindep
    rw [Fintype.card_fin] at h
    rw [sympSpan, show n - 1 = C.generatorsList.length from C.generators_length.symm]
    exact h
  have hind : LinearIndependent (ZMod 2) ![xv, zv] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    refine ⟨?_, ?_⟩
    · have h := congrArg (fun w => sympBilinForm n w zv) hst
      simp only [map_add, map_smul, map_zero, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.zero_apply, smul_eq_mul, hXZ, hZZ, _root_.mul_one, mul_zero, add_zero] at h
      exact h
    · have h := congrArg (fun w => sympBilinForm n w xv) hst
      simp only [map_add, map_smul, map_zero, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.zero_apply, smul_eq_mul, hXX, hZX, _root_.mul_one, mul_zero, zero_add] at h
      exact h
  have hfinU : finrank (ZMod 2) U = 2 := by
    rw [hU, show ({xv, zv} : Set (Fin (n + n) → ZMod 2)) = Set.range ![xv, zv] by
        ext w
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range, Fin.exists_fin_two,
          Matrix.cons_val_zero, Matrix.cons_val_one, eq_comm],
      finrank_span_eq_card hind, Fintype.card_fin]
  have hinf : sympSpan C.generatorsList ⊓ U = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    rw [Submodule.mem_inf] at hw
    obtain ⟨hwV, hwU⟩ := hw
    rw [hU, Submodule.mem_span_pair] at hwU
    obtain ⟨a, b, hab⟩ := hwU
    have hwz : sympBilinForm n w zv = 0 := LinearMap.BilinForm.isOrtho_def.mp
      ((LinearMap.BilinForm.mem_orthogonal_iff.mp hzv_V) w hwV)
    have hwx : sympBilinForm n w xv = 0 := LinearMap.BilinForm.isOrtho_def.mp
      ((LinearMap.BilinForm.mem_orthogonal_iff.mp hxv_V) w hwV)
    have ha : a = 0 := by
      have e : sympBilinForm n w zv = a := by
        rw [← hab]
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
          hXZ, hZZ, _root_.mul_one, mul_zero, add_zero]
      rw [hwz] at e; exact e.symm
    have hb : b = 0 := by
      have e : sympBilinForm n w xv = b := by
        rw [← hab]
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
          hXX, hZX, _root_.mul_one, mul_zero, zero_add]
      rw [hwx] at e; exact e.symm
    rw [← hab, ha, hb]; simp
  have hfinW : finrank (ZMod 2) ↥(sympSpan C.generatorsList ⊔ U) = n + 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (sympSpan C.generatorsList) U
    rw [hinf, finrank_bot, add_zero, hfinV, hfinU] at h
    omega
  have hfinOrth : finrank (ZMod 2) (LinearMap.BilinForm.orthogonal (sympBilinForm n)
      (sympSpan C.generatorsList ⊔ U)) = n - 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal sympBilinForm_nondegenerate,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hfinW]
    omega
  -- `V ⊆ Wᗮ`: the stabilizer is isotropic and commutes with the logicals.
  have hV_le : sympSpan C.generatorsList ≤ LinearMap.BilinForm.orthogonal (sympBilinForm n)
      (sympSpan C.generatorsList ⊔ U) := by
    rw [sympBilinForm_orthogonal_sup]
    refine le_inf ?_ ?_
    · rw [sympSpan, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, mem_sympBilinForm_orthogonal_span_iff]
      rintro _ ⟨j, rfl⟩
      exact hcomm _ (stabilizer_le_centralizer C.toStabilizerGroup
        (Subgroup.subset_closure (List.get_mem _ _))) j
    · rw [sympSpan, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, hU, mem_sympBilinForm_orthogonal_span_iff]
      intro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl
      · rw [hxv, symplecticBilinear_comm]; exact hcomm _ (C.logicalOps 0).x_mem_centralizer i
      · rw [hzv, symplecticBilinear_comm]; exact hcomm _ (C.logicalOps 0).z_mem_centralizer i
  -- `V = Wᗮ` (containment + equal finrank), so `symp(g) ∈ V`.
  rw [Submodule.eq_of_le_of_finrank_eq hV_le (by rw [hfinV, hfinOrth])]
  exact hgv_W

end Kernel

end Quantum.StabilizerGroup
