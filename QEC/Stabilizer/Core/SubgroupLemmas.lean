import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic

/-!
# Subgroup helper lemmas

This file collects small, reusable lemmas about `Subgroup.closure` that are useful when
constructing stabilizer groups:

- centralizer of a closure: membership iff commutes with every generator
- lifting commutation from generators to their closures
- proving a generated subgroup is abelian from pairwise commutation of generators

These are generic group-theoretic statements (no Pauli-specific content).
-/

namespace Subgroup

/-!
## Centralizer of a closure
-/

/-- An element lies in the centralizer of `closure S` iff it commutes with every
    element of `S`. So to show a logical operator is in the centralizer, it suffices
    to prove it commutes with each generator. -/
theorem mem_centralizer_closure_iff {G : Type*} [Group G] (g : G) (S : Set G) :
    g ∈ Subgroup.centralizer (closure S : Set G) ↔ ∀ s ∈ S, s * g = g * s := by
  constructor
  · intro hg s hs
    exact hg s (subset_closure hs)
  · intro hg h hh
    refine closure_induction (p := fun h _ => h * g = g * h) ?_ ?_ ?_ ?_ hh
    · intro s hs
      exact hg s hs
    · simp only [one_mul, mul_one]
    · intro x y _ _ hx hy
      calc (x * y) * g = x * (y * g) := by rw [mul_assoc]
        _ = x * (g * y) := by rw [hy]
        _ = (x * g) * y := by rw [mul_assoc]
        _ = (g * x) * y := by rw [hx]
        _ = g * (x * y) := by rw [mul_assoc]
    · intro x _ hx
      have H : (x⁻¹ * g) * x = (g * x⁻¹) * x := by
        rw [mul_assoc, ← hx, inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one]
      exact mul_right_cancel H

/-- Reformulation: (∀ h ∈ closure S, h * g = g * h) ↔ (∀ s ∈ S, s * g = g * s).
    Use this to rewrite a centralizer-membership goal into "commutes with each generator". -/
theorem forall_comm_closure_iff {G : Type*} [Group G] (g : G) (S : Set G) :
    (∀ h ∈ closure S, h * g = g * h) ↔ ∀ s ∈ S, s * g = g * s := by
  rw [← mem_centralizer_closure_iff, mem_centralizer_iff]; rfl

/-!
## Lifting commutation from generators to closures
-/

/-- If every generator in `S` commutes with every generator in `T`, then every element of
`closure S` commutes with every element of `closure T`. -/
theorem closure_commutes_of_commutes_generators
    {G : Type*} [Group G] {S T : Set G}
    (hST : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) :
    ∀ g ∈ closure S, ∀ k ∈ closure T, g * k = k * g := by
  intro g hg k hk
  have hg_comm : ∀ k ∈ closure T, g * k = k * g := by
    refine
      Subgroup.closure_induction
        (p := fun g (_ : g ∈ closure S) => ∀ k ∈ closure T, g * k = k * g)
        ?_ ?_ ?_ ?_ hg
    · intro s hs k hk
      refine Subgroup.closure_induction (p := fun k (_ : k ∈ closure T) => s * k = k * s)
        ?_ ?_ ?_ ?_ hk
      · intro t ht
        exact hST s hs t ht
      · simp
      · intro a b _ _ ha hb
        calc
          s * (a * b) = (s * a) * b := by simp [mul_assoc]
          _ = (a * s) * b := by simp [ha]
          _ = a * (s * b) := by simp [mul_assoc]
          _ = a * (b * s) := by simp [hb]
          _ = (a * b) * s := by simp [mul_assoc]
      · intro a _ ha
        have h' : s = a * (s * a⁻¹) := by
          have := congrArg (fun z => z * a⁻¹) ha
          simpa [mul_assoc] using this
        have h'' : a⁻¹ * s = s * a⁻¹ := by
          have := congrArg (fun z => a⁻¹ * z) h'
          simpa [mul_assoc] using this
        simpa [eq_comm] using h''
    · intro k hk'
      simp
    · intro a b _ _ ha hb k hk'
      calc
        (a * b) * k = a * (b * k) := by simp [mul_assoc]
        _ = a * (k * b) := by simp [hb k hk']
        _ = (a * k) * b := by simp [mul_assoc]
        _ = (k * a) * b := by simp [ha k hk']
        _ = k * (a * b) := by simp [mul_assoc]
    · intro a _ ha k hk'
      have h' : k = a⁻¹ * (k * a) := by
        have := congrArg (fun z => a⁻¹ * z) (ha k hk')
        simpa [mul_assoc] using this
      have h'' : k * a⁻¹ = a⁻¹ * k := by
        have := congrArg (fun z => z * a⁻¹) h'
        simpa [mul_assoc] using this
      simpa [eq_comm] using h''
  exact hg_comm k hk

/-!
## Abelian closure from commuting generators
-/

/-- If generators in `S` commute pairwise, then the subgroup `closure S` is abelian. -/
theorem abelian_closure_of_pairwise_commute
    {G : Type*} [Group G] (S : Set G)
    (hS : ∀ g ∈ S, ∀ h ∈ S, g * h = h * g) :
    ∀ g ∈ closure S, ∀ h ∈ closure S, g * h = h * g := by
  simpa using (closure_commutes_of_commutes_generators (S := S) (T := S) hS)

/-!
## Normal form in a commuting union

If `S` and `T` commute generatorwise, then every element of `closure (S ∪ T)` can be written
as a product `z * x` with `z ∈ closure S` and `x ∈ closure T`.

This is the key group-theoretic step behind the “CSS decomposition” proofs.
-/

/-- If generators in `S` commute with generators in `T`, then every element of `closure (S ∪ T)`
can be written as `z * x` with `z ∈ closure S` and `x ∈ closure T`. -/
theorem mem_closure_union_exists_mul_of_commute_generators
    {G : Type*} [Group G] {S T : Set G}
    (hST : ∀ s ∈ S, ∀ t ∈ T, s * t = t * s) :
    ∀ g, g ∈ closure (S ∪ T) → ∃ z ∈ closure S, ∃ x ∈ closure T, g = z * x := by
  classical
  have h_closure : ∀ z ∈ closure S, ∀ x ∈ closure T, z * x = x * z :=
    closure_commutes_of_commutes_generators (S := S) (T := T) hST
  intro g hg
  refine
    Subgroup.closure_induction
      (p := fun g (_ : g ∈ closure (S ∪ T)) =>
        ∃ z ∈ closure S, ∃ x ∈ closure T, g = z * x)
      ?_ ?_ ?_ ?_ hg
  · intro y hy
    rcases hy with hy | hy
    · refine ⟨y, subset_closure hy, 1, one_mem _, by simp⟩
    · refine ⟨1, one_mem _, y, subset_closure hy, by simp⟩
  · exact ⟨1, one_mem _, 1, one_mem _, by simp⟩
  · intro g₁ g₂ _ _ h₁ h₂
    rcases h₁ with ⟨z₁, hz₁, x₁, hx₁, rfl⟩
    rcases h₂ with ⟨z₂, hz₂, x₂, hx₂, rfl⟩
    refine ⟨z₁ * z₂, mul_mem hz₁ hz₂, x₁ * x₂, mul_mem hx₁ hx₂, ?_⟩
    have hxz : x₁ * z₂ = z₂ * x₁ := by
      simpa [eq_comm] using (h_closure z₂ hz₂ x₁ hx₁)
    calc
      (z₁ * x₁) * (z₂ * x₂) = z₁ * (x₁ * z₂) * x₂ := by simp [mul_assoc]
      _ = z₁ * (z₂ * x₁) * x₂ := by simp [hxz]
      _ = (z₁ * z₂) * (x₁ * x₂) := by simp [mul_assoc]
  · intro g _ h
    rcases h with ⟨z, hz, x, hx, rfl⟩
    have hzx : z * x = x * z := h_closure z hz x hx
    have h_inv : x⁻¹ * z⁻¹ = z⁻¹ * x⁻¹ := by
      simpa [mul_inv_rev] using congrArg Inv.inv hzx
    refine ⟨z⁻¹, inv_mem hz, x⁻¹, inv_mem hx, ?_⟩
    simp [mul_inv_rev, h_inv]

/-!
## Independent generating sets

A set S of generators is *independent* if no generator lies in the subgroup generated
by the others. This matches the textbook notion (e.g. Nielsen & Chuang). The equivalence
with symplectic row linear independence is proved separately (see BinarySymplectic).
-/

/-- A set `S` is an independent generating set if no element of `S` lies in the subgroup
generated by `S` with that element removed. -/
def IndependentGenerators {G : Type*} [Group G] (S : Set G) : Prop :=
  ∀ g ∈ S, g ∉ closure (S \ {g})

end Subgroup

