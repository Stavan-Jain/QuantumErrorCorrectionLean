import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic
import QEC.Stabilizer.BinarySymplectic.Core
import QEC.Stabilizer.BinarySymplectic.SymplecticInner
import QEC.Stabilizer.BinarySymplectic.CheckMatrix
import QEC.Stabilizer.BinarySymplectic.SymplecticSpan
import QEC.Stabilizer.Core.StabilizerGroup
import QEC.Stabilizer.Core.Centralizer
import QEC.Stabilizer.Core.LogicalOperatorCoset
import QEC.Stabilizer.Core.LogicalOperators
import QEC.Stabilizer.BinarySymplectic.IndependentEquiv
import QEC.Stabilizer.PauliGroup.NQubitOperator
import QEC.Stabilizer.PauliGroup.NQubitElement

namespace Quantum

open scoped BigOperators

variable {n : ℕ}

/-!
# Symplectic orthogonal and "no weight-w logical"

The symplectic bilinear form on F₂^{2n}: ⟨v,w⟩_s = (X-part of v)·(Z-part of w) +
(Z-part of v)·(X-part of w). The orthogonal of a submodule W is the set of v with
⟨v,w⟩_s = 0 for all w ∈ W. An operator commutes with all generators iff its
symplectic vector lies in the orthogonal of sympSpan L.

We also prove a generic lemma: if every weight-w operator that commutes with all
generators has its symplectic vector in sympSpan L, then no weight-w Pauli is a
nontrivial logical.
-/

namespace NQubitPauliOperator

/-- Symplectic bilinear form on vectors Fin (n + n) → ZMod 2. Matches the operator
    symplectic inner product when applied to toSymplectic images. -/
def symplecticBilinear (v w : Fin (n + n) → ZMod 2) : ZMod 2 :=
  (Finset.univ : Finset (Fin n)).sum (fun i =>
    v (Fin.castAdd n i) * w (Fin.natAdd n i) + v (Fin.natAdd n i) * w (Fin.castAdd n i))

/-- The bilinear form on toSymplectic images equals the operator symplectic inner. -/
theorem symplecticBilinear_toSymplectic (op₁ op₂ : NQubitPauliOperator n) :
    symplecticBilinear (toSymplectic op₁) (toSymplectic op₂) = symplecticInner op₁ op₂ := by
  unfold symplecticBilinear symplecticInner
  rw [Finset.sum_congr rfl fun i _ => ?_]
  simp only [toSymplectic_X_part, toSymplectic_Z_part]
  rfl

/-- The bilinear form is additive in the first argument. -/
lemma symplecticBilinear_add_left (v₁ v₂ w : Fin (n + n) → ZMod 2) :
    symplecticBilinear (v₁ + v₂) w = symplecticBilinear v₁ w + symplecticBilinear v₂ w := by
      unfold Quantum.NQubitPauliOperator.symplecticBilinear; simp +decide [
        Finset.sum_add_distrib, add_mul ] ; ring;

/-- The bilinear form is linear in the first argument under scalar multiplication. -/
lemma symplecticBilinear_smul_left (c : ZMod 2) (v w : Fin (n + n) → ZMod 2) :
    symplecticBilinear (c • v) w = c * symplecticBilinear v w := by
  unfold symplecticBilinear
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The bilinear form is additive in the second argument. -/
lemma symplecticBilinear_add_right (v w₁ w₂ : Fin (n + n) → ZMod 2) :
    symplecticBilinear v (w₁ + w₂) = symplecticBilinear v w₁ + symplecticBilinear v w₂ := by
      unfold Quantum.NQubitPauliOperator.symplecticBilinear; simp +decide [
        Finset.sum_add_distrib, mul_add ] ; ring;

/-- The bilinear form is linear in the second argument under scalar multiplication. -/
lemma symplecticBilinear_smul_right (c : ZMod 2) (v w : Fin (n + n) → ZMod 2) :
    symplecticBilinear v (c • w) = c * symplecticBilinear v w := by
  unfold symplecticBilinear
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end NQubitPauliOperator

namespace NQubitPauliGroupElement

open NQubitPauliOperator
open Submodule

/-- The symplectic orthogonal of a submodule W: vectors v with ⟨v, w⟩_s = 0 for all w ∈ W. -/
def sympOrthogonal (W : Submodule (ZMod 2) (Fin (n + n) → ZMod 2)) : Submodule
(ZMod 2) (Fin (n + n) → ZMod 2) where
  carrier := { v | ∀ w ∈ W, NQubitPauliOperator.symplecticBilinear v w = 0 }
  zero_mem' := fun _ _ => by simp only [NQubitPauliOperator.symplecticBilinear,
  Pi.zero_apply, zero_mul,
    add_zero, Finset.sum_const_zero]
  add_mem' := fun ha hb x hx => by
    rw [NQubitPauliOperator.symplecticBilinear_add_left, ha x hx, hb x hx, add_zero]
  smul_mem' := fun c v hv x hx => by
    rw [NQubitPauliOperator.symplecticBilinear_smul_left, hv x hx, mul_zero]

/-- An operator's symplectic vector is in the orthogonal of sympSpan L iff it commutes
    with every generator in L. -/
theorem mem_sympOrthogonal_sympSpan_iff (L : List (NQubitPauliGroupElement n))
(op : NQubitPauliOperator n) :
    NQubitPauliOperator.toSymplectic op ∈ sympOrthogonal (sympSpan L) ↔
      ∀ g ∈ L, NQubitPauliOperator.symplecticInner op g.operators = 0 := by
  rw [sympSpan, sympOrthogonal]
  simp only [Submodule.mem_mk]
  constructor
  · intro h g hg
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hg
    have h_mem : checkMatrix L i ∈ span (ZMod 2) (Set.range (checkMatrix L)) :=
      subset_span (Set.mem_range.mpr ⟨i, rfl⟩)
    have key := h (checkMatrix L i) h_mem
    rw [show checkMatrix L i = NQubitPauliOperator.toSymplectic
    (L.get i).operators from by ext j; rfl]
      at key
    rw [NQubitPauliOperator.symplecticBilinear_toSymplectic] at key
    rw [hi] at key
    exact key
  · intro h v hv
    induction hv using Submodule.span_induction with
    | mem v' hv' =>
      rcases hv' with ⟨k, rfl⟩
      rw [show checkMatrix L k = NQubitPauliOperator.toSymplectic
      (L.get k).operators from by ext j; rfl]
      rw [NQubitPauliOperator.symplecticBilinear_toSymplectic]
      exact h (L.get k) (List.mem_iff_get.mpr ⟨k, rfl⟩)
    | zero =>
      simp only [NQubitPauliOperator.symplecticBilinear, Pi.zero_apply, mul_zero, add_zero,
        Finset.sum_const_zero]
    | add a b _ _ ha hb =>
      rw [NQubitPauliOperator.symplecticBilinear_add_right, ha, hb, add_zero]
    | smul c x _ hx =>
      rw [NQubitPauliOperator.symplecticBilinear_smul_right, hx, mul_zero]

/-- If every weight-w operator that commutes with all generators has its symplectic
    vector in sympSpan L, then no weight-w Pauli is a nontrivial logical for the
    stabilizer group generated by L. -/
theorem no_weight_w_logical_of_centralizer_in_span (L : List (NQubitPauliGroupElement n))
    (S : StabilizerGroup n) (w : ℕ)
    (h_closure : S.toSubgroup = Subgroup.closure (listToSet L))
    (h_span : ∀ op : NQubitPauliOperator n, NQubitPauliOperator.weight op = w →
      (∀ g ∈ L, NQubitPauliOperator.symplecticInner op g.operators = 0) →
      NQubitPauliOperator.toSymplectic op ∈ sympSpan L)
    (g : NQubitPauliGroupElement n) (hg_weight : weight g = w)
    (hg_nontrivial : StabilizerGroup.IsNontrivialLogicalOperator g S) : False := by
  obtain ⟨h_cent, _, h_ops_ne⟩ :=
    (StabilizerGroup.IsNontrivialLogicalOperator_iff g S).mp hg_nontrivial
  rw [StabilizerGroup.mem_centralizer_iff_closure g S (listToSet L) h_closure] at h_cent
  have h_comm' : ∀ g' ∈ L, NQubitPauliOperator.symplecticInner g.operators g'.operators = 0 := by
    intro g' hg'
    exact (NQubitPauliOperator.commutes_iff_symplectic_inner_zero g g').1
      (Eq.symm (h_cent g' (by rw [listToSet, Set.mem_setOf]; exact hg')))
  have h_symp' : NQubitPauliOperator.toSymplectic g.operators ∈ sympSpan L :=
    h_span g.operators hg_weight h_comm'
  obtain ⟨s, hs_closure, hs_eq⟩ := exists_mem_closure_of_symp_in_span L g.operators h_symp'
  exact h_ops_ne s (h_closure ▸ hs_closure) hs_eq

end NQubitPauliGroupElement

end Quantum
