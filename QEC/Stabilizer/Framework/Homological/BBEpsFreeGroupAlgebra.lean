/-
# `EpsFree` for group algebras: coset-transversal freeness (A13 L2a, the wildcard)

`BBEpsFree.lean` reduced the general L2a to a single gap: the freeness of
the group algebra `k[G]` over the chain ring `Λ = k[X]/(X^N)` acting via
`X ↦ ε = x^σ − 1` (deck `σ` of order `N`).  This file closes that gap and
packages the payoff:

* `epsFree_single_sub_one_of_transversal` — the char-free core: if
  `(i, j) ↦ t i + j•σ` is a bijection `T × Fin N ≃ G` (a coset
  transversal of `⟨σ⟩` together with exactness of the order) and
  `ε^N = 0`, then `EpsFree ε N` holds in `AddMonoidAlgebra k G`.
  Proof: `{x^{t i}}` is a `Λ`-basis (spanning: `x^g = (X̄+1)^j • x^{t i}`;
  independence: canonical `modByMonic` representatives, the change of
  variable `p ↦ p ∘ (X−1)` turning `ε`-polynomials into `x^σ`-polynomials,
  and coefficient extraction at `t i₀ + m•σ`), so `epsFree_of_free`
  transports `epsFree_quotXpow` across it.
* `epsFree_one_add_single_of_addOrderOf` — the deck corollary: over a
  char-2 base, `σ` of order `2^r` gives `EpsFree (1 + x^σ) (2^r)` — the
  hypothesis consumed by BOTH `BBDeckTower.eps_mem_of_deckTrivial` (OQ1)
  and, through `hann_of_epsFree`, `BocksteinLift.bockstein_element_form`
  (OQ2).  The transversal is `Quotient.out` on `G ⧸ zmultiples σ`, and
  `ε^{2^r} = 0` is Frobenius.
-/

import QEC.Stabilizer.Framework.Homological.BBEpsFree
import QEC.Stabilizer.Framework.Homological.BocksteinLift
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace Quantum
namespace Stabilizer
namespace Homological
namespace BBEpsFree

open Polynomial BBDeckTower

/-! ## §0 Char-two Frobenius, instance-free -/

/-- Frobenius for exponent `2^r`, from the bare hypothesis `2 = 0` (no `CharP`
instances). -/
lemma add_pow_two_pow_of_two_eq_zero {A : Type*} [CommRing A]
    (h2 : (2 : A) = 0) (a b : A) (r : ℕ) :
    (a + b) ^ 2 ^ r = a ^ 2 ^ r + b ^ 2 ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hsq : ∀ x y : A, (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
      intro x y
      rw [add_sq, h2, zero_mul, zero_mul, add_zero]
    rw [pow_succ 2 r, pow_mul, pow_mul, pow_mul, ih, hsq]

/-! ## §1 Expansion and extraction in the group algebra -/

section GroupAlgebra

variable {k : Type*} [CommRing k] {G : Type*} [AddCommGroup G]

/-- `(x^σ)^j = x^{j•σ}`. -/
lemma single_pow_one (σ : G) (j : ℕ) :
    (AddMonoidAlgebra.single σ (1 : k)) ^ j
      = AddMonoidAlgebra.single (j • σ) 1 := by
  rw [AddMonoidAlgebra.single_pow, one_pow]

/-- **Expansion.** A polynomial in `x^σ` times a single `x^g` is the orbit sum
`∑_j q_j·x^{g + j•σ}`. -/
lemma aeval_single_mul_single (σ g : G) (c : k) {q : k[X]} {N : ℕ}
    (hq : q.natDegree < N) :
    Polynomial.aeval (AddMonoidAlgebra.single σ (1 : k)) q
        * AddMonoidAlgebra.single g c
      = ∑ j ∈ Finset.range N,
          AddMonoidAlgebra.single (g + j • σ) (q.coeff j * c) := by
  rw [Polynomial.aeval_eq_sum_range' hq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_assoc, single_pow_one, AddMonoidAlgebra.single_mul_single,
    AddMonoidAlgebra.smul_single', one_mul, add_comm (j • σ) g]

/-- **Extraction** (pure `Finsupp` level). Evaluating the orbit sum at `g + m•σ`
picks out the `m`-th coefficient, provided `j ↦ j•σ` is injective below `N`. -/
lemma sum_single_orbit_apply (σ g : G) (co : ℕ → k) {N : ℕ}
    (hinj : ∀ j < N, ∀ m < N, j • σ = m • σ → j = m)
    (m : ℕ) (hm : m < N) :
    (∑ j ∈ Finset.range N,
        Finsupp.single (g + j • σ) (co j) : G →₀ k) (g + m • σ) = co m := by
  classical
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single m]
  · rw [Finsupp.single_eq_same]
  · intro j hj hjm
    rw [Finsupp.single_apply, if_neg]
    intro hcon
    exact hjm (hinj j (Finset.mem_range.mp hj) m hm
      (by exact add_left_cancel hcon))
  · intro hcon
    exact absurd (Finset.mem_range.mpr hm) hcon

end GroupAlgebra

/-! ## §2 `EpsFree` at the `AdjoinRoot` presentation of the chain ring -/

/-- `epsFree_quotXpow` restated at `AdjoinRoot ((X)^N)` (definitionally the same
quotient; this is the form the algebra map below consumes). -/
lemma epsFree_adjoinRoot_root {R : Type*} [CommRing R] (N : ℕ) :
    EpsFree (AdjoinRoot.root ((X : R[X]) ^ N)) N :=
  epsFree_quotXpow N

/-! ## §3 The transversal basis

Context: `Λ = AdjoinRoot (X^N)` acts on `k[G]` through an algebra structure
characterized by `halg : algebraMap (mk p) = aeval (x^σ − 1) p` (supplied by
`AdjoinRoot.lift` in the main theorem). The family `i ↦ x^{t i}` for a
transversal `t : T → G` spans and is independent over `Λ`. -/

section Transversal

variable {k : Type*} [CommRing k] {G : Type*} [AddCommGroup G]
variable {σ : G} {N : ℕ}
variable [Algebra (AdjoinRoot ((X : k[X]) ^ N)) (AddMonoidAlgebra k G)]

/-- Spanning: every single `x^g c` is a `Λ`-multiple of a transversal element
(`g = t i + j•σ` ⟹ `x^g c = mk (C c·(X+1)^j) • x^{t i}`). -/
lemma span_transversal_eq_top
    (halg : ∀ p : k[X],
      algebraMap (AdjoinRoot ((X : k[X]) ^ N)) (AddMonoidAlgebra k G)
          (AdjoinRoot.mk _ p)
        = Polynomial.aeval (AddMonoidAlgebra.single σ (1 : k) - 1) p)
    {T : Type*} (t : T → G)
    (hsurj : Function.Surjective
      fun p : T × Fin N => t p.1 + (p.2 : ℕ) • σ) :
    ⊤ ≤ Submodule.span (AdjoinRoot ((X : k[X]) ^ N))
        (Set.range fun i => AddMonoidAlgebra.single (t i) (1 : k)) := by
  classical
  intro s _
  have hs : s = Finsupp.sum s fun g c => AddMonoidAlgebra.single g c :=
    (Finsupp.sum_single s).symm
  rw [hs]
  refine Submodule.finsuppSum_mem _ _ _ _ fun g _ => ?_
  obtain ⟨⟨i, j⟩, hij⟩ := hsurj g
  have hij' : t i + (j : ℕ) • σ = g := hij
  have key : (AdjoinRoot.mk ((X : k[X]) ^ N)
        (Polynomial.C (s g) * (X + 1) ^ (j : ℕ))) •
        AddMonoidAlgebra.single (t i) (1 : k)
      = AddMonoidAlgebra.single g (s g) := by
    rw [Algebra.smul_def, halg, map_mul, Polynomial.aeval_C, map_pow, map_add,
      Polynomial.aeval_X, Polynomial.aeval_one, sub_add_cancel, single_pow_one,
      mul_assoc, AddMonoidAlgebra.single_mul_single, one_mul,
      ← Algebra.smul_def, AddMonoidAlgebra.smul_single', mul_one,
      add_comm ((j : ℕ) • σ) (t i), hij']
  rw [← key]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Independence of the transversal family: expand each coefficient `l i ∈ Λ` by
its canonical `modByMonic` representative, change variables `p ↦ p ∘ (X−1)` to
turn `ε`-polynomials into `x^σ`-polynomials, and extract group-algebra
coefficients along the orbit `t i₀ + m•σ`. -/
lemma linearIndependent_transversal
    (halg : ∀ p : k[X],
      algebraMap (AdjoinRoot ((X : k[X]) ^ N)) (AddMonoidAlgebra k G)
          (AdjoinRoot.mk _ p)
        = Polynomial.aeval (AddMonoidAlgebra.single σ (1 : k) - 1) p)
    (hN : 0 < N) {T : Type*} (t : T → G)
    (hinj : Function.Injective
      fun p : T × Fin N => t p.1 + (p.2 : ℕ) • σ) :
    LinearIndependent (AdjoinRoot ((X : k[X]) ^ N))
      fun i => AddMonoidAlgebra.single (t i) (1 : k) := by
  classical
  rw [linearIndependent_iff]
  intro l hl
  rcases subsingleton_or_nontrivial k with hk | hk
  · haveI : Subsingleton (AdjoinRoot ((X : k[X]) ^ N)) :=
      AdjoinRoot.mk_surjective.subsingleton
    ext i
    exact Subsingleton.elim _ _
  -- degree bound for the changed-variable representatives
  have hdeg : ∀ i : T,
      ((AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow N) (l i)).comp
        ((X : k[X]) - 1)).natDegree < N := by
    intro i
    obtain ⟨P, hP⟩ := AdjoinRoot.mk_surjective (l i)
    have h1 : AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow N) (l i)
        = P %ₘ X ^ N := by
      rw [← hP, AdjoinRoot.modByMonicHom_mk]
    have hX1 : ((X : k[X]) - 1).natDegree = 1 := by
      rw [← Polynomial.C_1, Polynomial.natDegree_X_sub_C]
    have h2 : (P %ₘ X ^ N).natDegree < N := by
      by_cases h0 : P %ₘ X ^ N = 0
      · rw [h0, Polynomial.natDegree_zero]; exact hN
      · have := Polynomial.degree_modByMonic_lt P (Polynomial.monic_X_pow (R := k) N)
        rw [Polynomial.degree_X_pow] at this
        exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr this
    calc ((AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow N) (l i)).comp
            ((X : k[X]) - 1)).natDegree
        ≤ (AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow N) (l i)).natDegree
            * ((X : k[X]) - 1).natDegree := Polynomial.natDegree_comp_le
      _ = (P %ₘ X ^ N).natDegree := by rw [h1, hX1, mul_one]
      _ < N := h2
  -- the expanded linear combination
  have hl' : ∑ i ∈ l.support, ∑ j ∈ Finset.range N,
      AddMonoidAlgebra.single (t i + j • σ)
        (((AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow N) (l i)).comp
          ((X : k[X]) - 1)).coeff j * 1)
      = (0 : AddMonoidAlgebra k G) := by
    rw [← hl, Finsupp.linearCombination_apply]
    symm
    change ∑ i ∈ l.support, l i • AddMonoidAlgebra.single (t i) (1 : k) = _
    refine Finset.sum_congr rfl fun i _ => ?_
    have hLI := AdjoinRoot.mk_leftInverse (Polynomial.monic_X_pow N) (l i)
    rw [Algebra.smul_def]
    conv_lhs => rw [← hLI]
    rw [halg]
    have hcv : Polynomial.aeval (AddMonoidAlgebra.single σ (1 : k) - 1)
        (AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow N) (l i))
        = Polynomial.aeval (AddMonoidAlgebra.single σ (1 : k))
          ((AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow N) (l i)).comp
            ((X : k[X]) - 1)) := by
      rw [Polynomial.aeval_comp, map_sub, Polynomial.aeval_X,
        Polynomial.aeval_one]
    rw [hcv]
    exact aeval_single_mul_single σ (t i) 1 (hdeg i)
  ext i₀
  change l i₀ = 0
  by_cases hi₀ : i₀ ∈ l.support
  swap
  · exact Finsupp.notMem_support_iff.mp hi₀
  -- orbit-injectivity below N, from the pair injectivity
  have hinj' : ∀ j < N, ∀ m < N, j • σ = m • σ → j = m := by
    intro j hj m hm hsm
    have hpair : (i₀, (⟨j, hj⟩ : Fin N)) = (i₀, (⟨m, hm⟩ : Fin N)) := by
      apply hinj
      change t i₀ + j • σ = t i₀ + m • σ
      rw [hsm]
    have := congrArg (fun p : T × Fin N => (p.2 : ℕ)) hpair
    exact this
  -- coefficient extraction along the i₀-orbit
  have hcoeff : ∀ m < N,
      ((AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow N) (l i₀)).comp
        ((X : k[X]) - 1)).coeff m = 0 := by
    intro m hm
    have happ : (∑ i ∈ l.support, ∑ j ∈ Finset.range N,
        Finsupp.single (t i + j • σ)
          (((AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow N) (l i)).comp
            ((X : k[X]) - 1)).coeff j * 1) : G →₀ k) (t i₀ + m • σ)
        = (0 : G →₀ k) (t i₀ + m • σ) :=
      congrArg (fun v : G →₀ k => v (t i₀ + m • σ)) hl'
    rw [Finsupp.finsetSum_apply, Finsupp.zero_apply] at happ
    have hside : ∀ i ∈ l.support, i ≠ i₀ →
        (∑ j ∈ Finset.range N, Finsupp.single (t i + j • σ)
          (((AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow N) (l i)).comp
            ((X : k[X]) - 1)).coeff j * 1) : G →₀ k) (t i₀ + m • σ) = 0 := by
      intro i _ hii₀
      rw [Finsupp.finsetSum_apply]
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Finsupp.single_apply, if_neg]
      intro hcon
      exact hii₀ (congrArg Prod.fst (hinj (a₁ := (i, ⟨j, Finset.mem_range.mp hj⟩))
        (a₂ := (i₀, ⟨m, hm⟩)) hcon))
    have hnotmem : i₀ ∉ l.support →
        (∑ j ∈ Finset.range N, Finsupp.single (t i₀ + j • σ)
          (((AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow N) (l i₀)).comp
            ((X : k[X]) - 1)).coeff j * 1) : G →₀ k) (t i₀ + m • σ) = 0 :=
      fun hcon => absurd hi₀ hcon
    rw [Finset.sum_eq_single i₀ hside hnotmem] at happ
    have hF := sum_single_orbit_apply σ (t i₀)
      (fun j => ((AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow N)
        (l i₀)).comp ((X : k[X]) - 1)).coeff j * 1) hinj' m hm
    rw [hF] at happ
    simpa using happ
  -- the changed-variable representative vanishes …
  have hq0 : (AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow N) (l i₀)).comp
      ((X : k[X]) - 1) = 0 := by
    ext m
    rcases lt_or_ge m N with hm | hm
    · rw [hcoeff m hm, Polynomial.coeff_zero]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hdeg i₀) hm),
        Polynomial.coeff_zero]
  -- … hence so does the representative, hence `l i₀`
  have hp0 : AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow N) (l i₀) = 0 := by
    have hcomp := congrArg (fun r : k[X] => r.comp ((X : k[X]) + 1)) hq0
    simpa [Polynomial.comp_assoc, Polynomial.sub_comp, Polynomial.X_comp,
      Polynomial.one_comp, add_sub_cancel_right] using hcomp
  have hLI := AdjoinRoot.mk_leftInverse (Polynomial.monic_X_pow N) (l i₀)
  rw [← hLI, hp0, map_zero]

end Transversal

/-! ## §4 The main theorem: `EpsFree` in the group algebra -/

/-- **The L2a wildcard, char-free core.** If `(i, j) ↦ t i + j•σ` is a bijection
`T × Fin N ≃ G` (coset transversal + exact order) and `ε = x^σ − 1` satisfies
`ε^N = 0`, then `EpsFree ε N` holds in `AddMonoidAlgebra k G`: the group algebra
is free over the chain ring `k[X]/(X^N)` on the transversal, so
`epsFree_quotXpow` transports across (`epsFree_of_free`). -/
theorem epsFree_single_sub_one_of_transversal
    {k : Type*} [CommRing k] {G : Type*} [AddCommGroup G] {σ : G} {N : ℕ}
    (hN : 0 < N)
    (hεN : (AddMonoidAlgebra.single σ (1 : k) - 1) ^ N = 0)
    {T : Type*} (t : T → G)
    (he : Function.Bijective fun p : T × Fin N => t p.1 + (p.2 : ℕ) • σ) :
    EpsFree (AddMonoidAlgebra.single σ (1 : k) - 1) N := by
  have hev : ((X : k[X]) ^ N).eval₂
      (algebraMap k (AddMonoidAlgebra k G))
      (AddMonoidAlgebra.single σ (1 : k) - 1) = 0 := by
    rw [Polynomial.eval₂_X_pow]
    exact hεN
  letI : Algebra (AdjoinRoot ((X : k[X]) ^ N)) (AddMonoidAlgebra k G) :=
    (AdjoinRoot.lift (algebraMap k (AddMonoidAlgebra k G))
      (AddMonoidAlgebra.single σ (1 : k) - 1) hev).toAlgebra
  have halg : ∀ p : k[X],
      algebraMap (AdjoinRoot ((X : k[X]) ^ N)) (AddMonoidAlgebra k G)
          (AdjoinRoot.mk _ p)
        = Polynomial.aeval (AddMonoidAlgebra.single σ (1 : k) - 1) p := by
    intro p
    rw [RingHom.algebraMap_toAlgebra, AdjoinRoot.lift_mk, Polynomial.aeval_def]
  letI : Module.Free (AdjoinRoot ((X : k[X]) ^ N)) (AddMonoidAlgebra k G) :=
    Module.Free.of_basis (Module.Basis.mk
      (linearIndependent_transversal halg hN t he.injective)
      (span_transversal_eq_top halg t he.surjective))
  have h := epsFree_of_free (S := AddMonoidAlgebra k G)
    (epsFree_adjoinRoot_root (R := k) N)
  have hroot : algebraMap (AdjoinRoot ((X : k[X]) ^ N)) (AddMonoidAlgebra k G)
      (AdjoinRoot.root ((X : k[X]) ^ N))
      = AddMonoidAlgebra.single σ (1 : k) - 1 := by
    have hr : AdjoinRoot.root ((X : k[X]) ^ N)
        = AdjoinRoot.mk ((X : k[X]) ^ N) X := rfl
    rw [hr, halg, Polynomial.aeval_X]
  rwa [hroot] at h

/-! ## §5 The canonical transversal: `Quotient.out` on `G ⧸ ⟨σ⟩` -/

/-- For `σ` of exact order `N`, `(q, j) ↦ q.out + j•σ` is a bijection
`(G ⧸ ⟨σ⟩) × Fin N ≃ G`: `Quotient.out` is a coset transversal, and the orbit
coordinates below the order are distinct. -/
lemma transversal_out_bijective {G : Type*} [AddCommGroup G] (σ : G) {N : ℕ}
    (hord : addOrderOf σ = N) (hN : 0 < N) :
    Function.Bijective
      fun p : (G ⧸ AddSubgroup.zmultiples σ) × Fin N =>
        Quotient.out p.1 + (p.2 : ℕ) • σ := by
  set φ := QuotientAddGroup.mk' (AddSubgroup.zmultiples σ) with hφ
  have hφ_out : ∀ q : G ⧸ AddSubgroup.zmultiples σ, φ (Quotient.out q) = q :=
    fun q => Quotient.out_eq' q
  have hφσ : φ σ = 0 :=
    (QuotientAddGroup.eq_zero_iff σ).mpr (AddSubgroup.mem_zmultiples σ)
  have hφ_smul : ∀ j : ℕ, φ (j • σ) = 0 := by
    intro j
    rw [map_nsmul, hφσ, smul_zero]
  constructor
  · rintro ⟨q, j⟩ ⟨q', j'⟩ h
    have h' : Quotient.out q + (j : ℕ) • σ = Quotient.out q' + (j' : ℕ) • σ := h
    have hq : q = q' := by
      have h2 := DFunLike.congr_arg φ h'
      rwa [map_add, map_add, hφ_smul, hφ_smul, add_zero, add_zero,
        hφ_out, hφ_out] at h2
    subst hq
    have hsm : (j : ℕ) • σ = (j' : ℕ) • σ := by
      have h2 := h'
      rwa [add_right_inj] at h2
    have hjj' : (j : ℕ) = (j' : ℕ) := by
      rcases le_total (j : ℕ) (j' : ℕ) with hle | hle
      · have hz : ((j' : ℕ) - (j : ℕ)) • σ = 0 := by
          rw [sub_nsmul σ hle, hsm]
          exact add_neg_cancel _
        have hdvd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz
        rw [hord] at hdvd
        have hlt : (j' : ℕ) - (j : ℕ) < N := lt_of_le_of_lt (Nat.sub_le _ _) j'.isLt
        have h0 : (j' : ℕ) - (j : ℕ) = 0 := by
          rcases Nat.eq_zero_or_pos ((j' : ℕ) - (j : ℕ)) with h | hpos
          · exact h
          · exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hlt)
        omega
      · have hz : ((j : ℕ) - (j' : ℕ)) • σ = 0 := by
          rw [sub_nsmul σ hle, ← hsm]
          exact add_neg_cancel _
        have hdvd := addOrderOf_dvd_iff_nsmul_eq_zero.mpr hz
        rw [hord] at hdvd
        have hlt : (j : ℕ) - (j' : ℕ) < N := lt_of_le_of_lt (Nat.sub_le _ _) j.isLt
        have h0 : (j : ℕ) - (j' : ℕ) = 0 := by
          rcases Nat.eq_zero_or_pos ((j : ℕ) - (j' : ℕ)) with h | hpos
          · exact h
          · exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hlt)
        omega
    exact Prod.ext rfl (Fin.ext hjj')
  · intro g
    have hmem : g - Quotient.out (φ g) ∈ AddSubgroup.zmultiples σ := by
      have h0 : φ (g - Quotient.out (φ g)) = 0 := by
        rw [map_sub, hφ_out, sub_self]
      exact (QuotientAddGroup.eq_zero_iff _).mp h0
    obtain ⟨z, hz⟩ := AddSubgroup.mem_zmultiples_iff.mp hmem
    have h1 : 0 ≤ z % (N : ℤ) := Int.emod_nonneg z (by exact_mod_cast hN.ne')
    have h2 : z % (N : ℤ) < (N : ℤ) := Int.emod_lt_of_pos z (by exact_mod_cast hN)
    refine ⟨⟨φ g, ⟨(z % (N : ℤ)).toNat, by omega⟩⟩, ?_⟩
    change Quotient.out (φ g) + (z % (N : ℤ)).toNat • σ = g
    have hNσ : (N : ℤ) • σ = 0 := by
      rw [natCast_zsmul, ← hord]
      exact addOrderOf_nsmul_eq_zero σ
    have hzred : (z % (N : ℤ)).toNat • σ = z • σ := by
      calc (z % (N : ℤ)).toNat • σ
          = ((z % (N : ℤ)).toNat : ℤ) • σ := (natCast_zsmul _ _).symm
        _ = (z % (N : ℤ)) • σ := by rw [Int.toNat_of_nonneg h1]
        _ = (z - (N : ℤ) * (z / (N : ℤ))) • σ := by rw [Int.emod_def]
        _ = z • σ - ((N : ℤ) * (z / (N : ℤ))) • σ := by
            rw [sub_zsmul, ← sub_eq_add_neg]
        _ = z • σ := by
            rw [mul_comm, mul_zsmul, hNσ, smul_zero, sub_zero]
    rw [hzred, hz]
    rw [add_comm, sub_add_cancel]

/-! ## §6 The deck corollary: `EpsFree (1 + x^σ) (2^r)` -/

/-- **The L2a wildcard, deck form.** Over a char-2 base, a deck `σ` of exact
order `2^r` yields `EpsFree (1 + x^σ) (2^r)` in `k[G]` — the shared ring
hypothesis of the OQ1 tower (`BBDeckTower.eps_mem_of_deckTrivial`) and, through
`hann_of_epsFree`, of the OQ2 element form
(`BocksteinLift.bockstein_element_form`). -/
theorem epsFree_one_add_single_of_addOrderOf
    {k : Type*} [CommRing k] (h2 : (2 : k) = 0)
    {G : Type*} [AddCommGroup G] (σ : G) (r : ℕ)
    (hord : addOrderOf σ = 2 ^ r) :
    EpsFree (1 + AddMonoidAlgebra.single σ (1 : k)) (2 ^ r) := by
  have hN : 0 < 2 ^ r := pow_pos two_pos r
  have h2S : (2 : AddMonoidAlgebra k G) = 0 := by
    rw [← map_ofNat (algebraMap k (AddMonoidAlgebra k G)) 2, h2, map_zero]
  have hneg1 : (-1 : AddMonoidAlgebra k G) = 1 := by
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two]
    exact h2S
  have hswap : 1 + AddMonoidAlgebra.single σ (1 : k)
      = AddMonoidAlgebra.single σ (1 : k) - 1 := by
    rw [sub_eq_add_neg, hneg1,
      add_comm (1 : AddMonoidAlgebra k G) (AddMonoidAlgebra.single σ (1 : k))]
  have hy : (AddMonoidAlgebra.single σ (1 : k)) ^ (2 ^ r) = 1 := by
    rw [single_pow_one, ← hord, addOrderOf_nsmul_eq_zero]
    exact AddMonoidAlgebra.one_def.symm
  have hεN : (AddMonoidAlgebra.single σ (1 : k) - 1) ^ (2 ^ r) = 0 := by
    have hfr := add_pow_two_pow_of_two_eq_zero h2S
      (AddMonoidAlgebra.single σ (1 : k)) (-1) r
    rw [← sub_eq_add_neg] at hfr
    rw [hfr, hy, hneg1, one_pow, one_add_one_eq_two]
    exact h2S
  rw [hswap]
  exact epsFree_single_sub_one_of_transversal hN hεN Quotient.out
    (transversal_out_bijective σ hord hN)

/-! ## §7 Wiring L2a into L1: the element form for real deck group algebras -/

/-- **Element form for order-4 deck group algebras (L1 ∘ L2a).** The L2a
freeness (`epsFree_one_add_single_of_addOrderOf` at `r = 2`, so
`addOrderOf σ = 4`) supplies through `hann_of_epsFree` exactly the
`Ann(ε) = (ε³)` hypothesis that L1's abstract capstone
`BocksteinLift.bockstein_element_form` consumes. Composing them: for a deck `σ`
of exact order 4 over any char-2 base, with `ε = 1 + x^σ`, the Bockstein element
form `δ₁ ∘ δ₂ = 0` holds **unconditionally** in the cover quotient `k[G] ⧸ (ε²)`
— whenever `A z̄ = ε ā` and `B z̄ = ε b̄`, the representative `A b̄ + B ā` lies
in `ε·(A, B)`.

This discharges, for the Frattini-lift ring of every genuine BB double cover,
the ring hypothesis L1 had to assume. What remains to reach the homological
equality `E = k̃ − k` (`BBTransferH1.BocksteinVanishes`) is the
seam↔connecting-map identification transporting this element fact onto `H₁`. -/
theorem bockstein_element_form_group_algebra
    {k : Type*} [CommRing k] (h2 : (2 : k) = 0)
    {G : Type*} [AddCommGroup G] (σ : G) (hord : addOrderOf σ = 4)
    (A B : AddMonoidAlgebra k G)
    (z a b : AddMonoidAlgebra k G ⧸
      Ideal.span {(1 + AddMonoidAlgebra.single σ (1 : k)) ^ 2})
    (hAz : Ideal.Quotient.mk _ A * z
      = Ideal.Quotient.mk _ (1 + AddMonoidAlgebra.single σ (1 : k)) * a)
    (hBz : Ideal.Quotient.mk _ B * z
      = Ideal.Quotient.mk _ (1 + AddMonoidAlgebra.single σ (1 : k)) * b) :
    Ideal.Quotient.mk _ A * b + Ideal.Quotient.mk _ B * a ∈
      Ideal.span
        {Ideal.Quotient.mk (Ideal.span {(1 + AddMonoidAlgebra.single σ (1 : k)) ^ 2})
            (1 + AddMonoidAlgebra.single σ (1 : k)) * Ideal.Quotient.mk _ A,
          Ideal.Quotient.mk (Ideal.span {(1 + AddMonoidAlgebra.single σ (1 : k)) ^ 2})
            (1 + AddMonoidAlgebra.single σ (1 : k)) * Ideal.Quotient.mk _ B} := by
  have hchar : (2 : AddMonoidAlgebra k G) = 0 := by
    rw [← map_ofNat (algebraMap k (AddMonoidAlgebra k G)) 2, h2, map_zero]
  have hEF : EpsFree (1 + AddMonoidAlgebra.single σ (1 : k)) 4 := by
    have h := epsFree_one_add_single_of_addOrderOf h2 σ 2 (hord.trans (by norm_num))
    norm_num at h
    exact h
  exact BocksteinLift.bockstein_element_form _ A B hchar
    (hann_of_epsFree hEF) z a b hAz hBz

end BBEpsFree
end Homological
end Stabilizer
end Quantum
