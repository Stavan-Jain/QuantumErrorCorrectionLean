import Mathlib.Tactic
import QEC.Stabilizer.Core.CSSNoNegI
import QEC.Stabilizer.PauliGroup.Commutation

namespace Quantum
namespace StabilizerGroup
namespace CSSCommutationLemmas

open NQubitPauliGroupElement

/-- Any two Z-type elements commute. -/
lemma ZType_commutes {n : ℕ} {g h : NQubitPauliGroupElement n}
    (hg : NQubitPauliGroupElement.IsZTypeElement g)
    (hh : NQubitPauliGroupElement.IsZTypeElement h) :
    g * h = h * g := by
  apply NQubitPauliGroupElement.commutes_of_componentwise_commutes g h
  intro i
  have h_op : ∀ i, g.operators i = .I ∨ g.operators i = .Z := fun j => hg.2 j
  have h_op' : ∀ i, h.operators i = .I ∨ h.operators i = .Z := fun j => hh.2 j
  cases h_op i <;> cases h_op' i <;> simp +decide [*]

/-- Any two X-type elements commute. -/
lemma XType_commutes {n : ℕ} {g h : NQubitPauliGroupElement n}
    (hg : NQubitPauliGroupElement.IsXTypeElement g)
    (hh : NQubitPauliGroupElement.IsXTypeElement h) :
    g * h = h * g := by
  apply NQubitPauliGroupElement.commutes_of_componentwise_commutes g h
  intro i
  have h_op : ∀ i, g.operators i = .I ∨ g.operators i = .X := fun j => hg.2 j
  have h_op' : ∀ i, h.operators i = .I ∨ h.operators i = .X := fun j => hh.2 j
  cases h_op i <;> cases h_op' i <;> simp +decide [*]

/-- Convenience wrapper for the standard CSS no-`-I` closure lemma. -/
theorem negIdentity_not_mem_closure_union
    {n : ℕ}
    (ZGenerators XGenerators : Set (NQubitPauliGroupElement n))
    (hZ : ∀ z, z ∈ ZGenerators → NQubitPauliGroupElement.IsZTypeElement z)
    (hX : ∀ x, x ∈ XGenerators → NQubitPauliGroupElement.IsXTypeElement x)
    (hZX : ∀ z ∈ ZGenerators, ∀ x ∈ XGenerators, z * x = x * z) :
    StabilizerGroup.negIdentity n ∉ Subgroup.closure (ZGenerators ∪ XGenerators) := by
  exact CSS.negIdentity_not_mem_closure_union ZGenerators XGenerators hZ hX hZX

end CSSCommutationLemmas
end StabilizerGroup
end Quantum

