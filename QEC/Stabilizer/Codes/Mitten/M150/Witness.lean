/-
# The weight-10 distance witness of the `[[150,30,10]]` mitten code

M3 of the mitten certification.  The generated `witSup` (weight 10,
`∈ ker H_X`) is a dual cycle of `m150Complex` that is **not** a dual
boundary, certified by the explicit pairing chain `witPairSup`
(`∈ ker H_Z`, inner product `1`) through
`HomologicalCode.not_mem_dualBoundaries_of_witness`.

Headline (`m150_exists_weight10_nontrivial_dualCycle`): the mitten
complex has a weight-10 nontrivial Z-logical chain — the kernel-checked
`d ≤ 10` half of the distance; the `≥ 10` floors are the M4 stage of the
attempt.  Provenance:
`qec-lab:experiments/bb_lab/scripts/m150_gen_lean_data.py` (witness
validated in numpy before emission; SAT ground truth
`qec-lab:experiments/bb_lab/certificates/mitten_150_30_10_{X,Z}.cert.json`).
-/

import QEC.Stabilizer.Codes.Mitten.M150.StabilizerCode

namespace Quantum
namespace Stabilizer
namespace Homological
namespace LP
namespace M150

open scoped BigOperators

/-- The weight-10 witness 1-chain (indicator of `witSup`). -/
def witChain : Fin 5 × M150G → ZMod 2 :=
  fun q => if q ∈ witSup.map qubitOf then 1 else 0

/-- Its dual pairing 1-chain (indicator of `witPairSup`, weight 18). -/
def witPairChain : Fin 5 × M150G → ZMod 2 :=
  fun q => if q ∈ witPairSup.map qubitOf then 1 else 0

/-- Batched computational facts (one `native_decide`): `witChain ∈ ker H_X`
(via `dualBfn`), `witPairChain ∈ ker H_Z` (via `lpBoundary1Fn`), odd
pairing, weight 10. -/
private lemma wit_facts :
    (∀ p : Fin 2 × M150G, dualBfn witChain p = 0)
    ∧ (∀ p : Fin 2 × M150G, lpBoundary1Fn m150A m150B witPairChain p = 0)
    ∧ ((∑ q : Fin 5 × M150G, witPairChain q * witChain q) = 1)
    ∧ ((Finset.univ.filter fun q : Fin 5 × M150G => witChain q ≠ 0).card = 10) := by
  native_decide

/-- The witness is a dual cycle (`∈ ker H_X`). -/
theorem witChain_dualBoundary : m150Complex.dualBoundary witChain = 0 := by
  funext p
  rw [dualBoundary_eq_dualBfn]
  exact wit_facts.1 p

/-- The pairing chain is a cycle (`∈ ker H_Z`). -/
theorem witPairChain_boundary1 : m150Complex.boundary1 witPairChain = 0 := by
  funext p
  exact wit_facts.2.1 p

/-- The pairing is odd: `⟨witPairChain, witChain⟩ = 1`. -/
theorem witPair_pairing :
    ∑ e : Fin 5 × M150G, witPairChain e * witChain e = 1 :=
  wit_facts.2.2.1

/-- The witness has chain weight exactly 10. -/
theorem chainWeight_witChain : m150Complex.chainWeight witChain = 10 := by
  rw [show m150Complex.chainWeight witChain
      = (Finset.univ.filter fun q : Fin 5 × M150G => witChain q ≠ 0).card
      from rfl]
  exact wit_facts.2.2.2

/-- The witness is not a dual boundary (dual-witness certificate). -/
theorem witChain_not_mem_dualBoundaries :
    witChain ∉ m150Complex.dualBoundaries :=
  HomologicalCode.not_mem_dualBoundaries_of_witness witPairChain_boundary1
    witPair_pairing

/-- **The `[[150,30,10]]` mitten complex has a weight-10 nontrivial
Z-logical chain** — the kernel-checked `d ≤ 10` half of the distance (the
`≥ 10` floors are the M4 stage of the attempt). -/
theorem m150_exists_weight10_nontrivial_dualCycle :
    ∃ v ∈ m150Complex.dualCycles,
      v ∉ m150Complex.dualBoundaries ∧ m150Complex.chainWeight v = 10 :=
  ⟨witChain, LinearMap.mem_ker.mpr witChain_dualBoundary,
    witChain_not_mem_dualBoundaries, chainWeight_witChain⟩

end M150
end LP
end Homological
end Stabilizer
end Quantum
