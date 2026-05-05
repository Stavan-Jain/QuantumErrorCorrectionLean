import QEC.Stabilizer.Homological.Generators
import QEC.Stabilizer.Core.SubgroupLemmas
import QEC.Stabilizer.Core.StabilizerGroup
import QEC.Stabilizer.Core.CSSNoNegI

/-!
# §B.3 — Generic CSS stabilizer group from a homological code

This file constructs `homologicalStabilizerGroup X : StabilizerGroup X.numQubits`
from the generators defined in §B.2.  The generators pairwise commute (§B.2)
and their closure does not contain `-I` (standard CSS argument), so this
packages directly as a `StabilizerGroup`.

The full `StabilizerCode` construction (which adds logical operators per
H₁ basis element, plus the symplectic-LI proof) is left to each instance
since it depends on instance-specific kernel data and a basis of `H₁`.
-/

namespace Quantum
namespace Stabilizer
namespace Homological

open scoped BigOperators

namespace HomologicalCode

variable (X : HomologicalCode)

/-- The full generator set of the CSS code: union of vertex and face stabilizers. -/
noncomputable def homologicalGenerators :
    Set (NQubitPauliGroupElement X.numQubits) :=
  X.ZGenerators ∪ X.XGenerators

variable {X}

/-- Z-generators are inside the full generator set. -/
lemma ZGenerators_subset_homologicalGenerators :
    X.ZGenerators ⊆ X.homologicalGenerators :=
  Set.subset_union_left

/-- X-generators are inside the full generator set. -/
lemma XGenerators_subset_homologicalGenerators :
    X.XGenerators ⊆ X.homologicalGenerators :=
  Set.subset_union_right

/-- All generators pairwise commute (combining X-X, Z-Z, and X-Z arguments from §B.2). -/
lemma homologicalGenerators_commute :
    ∀ g ∈ X.homologicalGenerators, ∀ h ∈ X.homologicalGenerators, g * h = h * g := by
  rintro g (hg | hg) h (hh | hh)
  -- Z, Z
  · exact Quantum.StabilizerGroup.CSSCommutationLemmas.ZType_commutes
      (ZGenerators_isZType _ hg) (ZGenerators_isZType _ hh)
  -- Z, X
  · exact ZGenerators_commute_XGenerators _ hg _ hh
  -- X, Z
  · exact (ZGenerators_commute_XGenerators _ hh _ hg).symm
  -- X, X
  · exact Quantum.StabilizerGroup.CSSCommutationLemmas.XType_commutes
      (XGenerators_isXType _ hg) (XGenerators_isXType _ hh)

variable (X)

/-- The closure of the homological generators does not contain `-I`. -/
lemma negIdentity_not_mem_closure_homologicalGenerators :
    Quantum.StabilizerGroup.negIdentity X.numQubits ∉
      Subgroup.closure X.homologicalGenerators := by
  unfold homologicalGenerators
  exact Quantum.StabilizerGroup.CSSCommutationLemmas.negIdentity_not_mem_closure_union
    X.ZGenerators X.XGenerators
    ZGenerators_isZType XGenerators_isXType ZGenerators_commute_XGenerators

/-- The CSS stabilizer group of a homological code. -/
noncomputable def homologicalStabilizerGroup :
    Quantum.StabilizerGroup X.numQubits where
  toSubgroup := Subgroup.closure X.homologicalGenerators
  is_abelian := fun g h hg hh =>
    Subgroup.abelian_closure_of_pairwise_commute X.homologicalGenerators
      homologicalGenerators_commute g hg h hh
  no_neg_identity := negIdentity_not_mem_closure_homologicalGenerators X

/-- The stabilizer group's subgroup is the closure of the generator set. -/
@[simp] lemma homologicalStabilizerGroup_toSubgroup :
    (X.homologicalStabilizerGroup).toSubgroup =
      Subgroup.closure X.homologicalGenerators := rfl

/-- The stabilizer group's subgroup, expressed as the closure of `Z ∪ X` generators. -/
lemma homologicalStabilizerGroup_toSubgroup_union :
    (X.homologicalStabilizerGroup).toSubgroup =
      Subgroup.closure (X.ZGenerators ∪ X.XGenerators) := rfl

end HomologicalCode

end Homological
end Stabilizer
end Quantum
