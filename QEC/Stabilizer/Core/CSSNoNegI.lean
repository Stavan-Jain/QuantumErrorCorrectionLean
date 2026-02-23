import Mathlib.Tactic
import QEC.Stabilizer.Core.StabilizerGroup
import QEC.Stabilizer.Core.SubgroupLemmas
import QEC.Stabilizer.Core.CSS

namespace Quantum

/-!
# CSS: excluding `negIdentity`

This file packages a reusable “no `-I`” criterion for **CSS-generated** subgroups.

The proof is purely algebraic:
- assume generators split into `ZGen` and `XGen` that commute generatorwise
- use `Subgroup.mem_closure_union_exists_mul_of_commute_generators` to decompose any element
  of `closure (ZGen ∪ XGen)` as `z * x` with `z ∈ closure ZGen` and `x ∈ closure XGen`
- show `z` is Z-type and `x` is X-type (closure invariants from `CSS.lean`)
- if `z * x` has identity operators then it must be `1` (cross-type identity lemma)
- apply to `negIdentity n`, whose operators are identity but which is not `1`
- conclude `negIdentity n ∉ closure (ZGen ∪ XGen)`
-/

namespace CSS

open StabilizerGroup NQubitPauliGroupElement

/-- If `ZGen` and `XGen` are phase-0 Z-type / X-type generators that commute generatorwise,
then `negIdentity n` is not in the subgroup they generate. -/
theorem negIdentity_not_mem_closure_union
    {n : ℕ} (ZGen XGen : Set (NQubitPauliGroupElement n))
    (hZ : ∀ z, z ∈ ZGen → NQubitPauliGroupElement.IsZTypeElement z)
    (hX : ∀ x, x ∈ XGen → NQubitPauliGroupElement.IsXTypeElement x)
    (hZX : ∀ z ∈ ZGen, ∀ x ∈ XGen, z * x = x * z) :
    negIdentity n ∉ Subgroup.closure (ZGen ∪ XGen) := by
  intro hneg
  -- Decompose `negIdentity n` as `z * x` with `z ∈ closure ZGen`, `x ∈ closure XGen`.
  obtain ⟨z, hz, x, hx, hzx⟩ :
      ∃ z ∈ Subgroup.closure ZGen, ∃ x ∈ Subgroup.closure XGen, negIdentity n = z * x := by
    simpa using
      (Subgroup.mem_closure_union_exists_mul_of_commute_generators (S := ZGen) (T := XGen) hZX
        (negIdentity n) hneg)
  -- Lift the typing invariants to the closures.
  have hz_ty : NQubitPauliGroupElement.IsZTypeElement z :=
    NQubitPauliGroupElement.IsZTypeElement_of_mem_closure (S := ZGen) hZ z hz
  have hx_ty : NQubitPauliGroupElement.IsXTypeElement x :=
    NQubitPauliGroupElement.IsXTypeElement_of_mem_closure (S := XGen) hX x hx
  -- Use the identity-operators criterion to conclude `z * x = 1`.
  have h_op : (z * x).operators = NQubitPauliOperator.identity n := by
    -- `negIdentity` has identity operators.
    simpa [hzx, negIdentity] using (congrArg NQubitPauliGroupElement.operators hzx).symm
  have : z * x = 1 :=
    NQubitPauliGroupElement.z_mul_x_eq_one_of_operators_eq_identity z x hz_ty hx_ty h_op
  -- Contradiction: `negIdentity n ≠ 1`.
  exact negIdentity_ne_one n (by simpa [hzx] using this)

end CSS

end Quantum

