/-
# The `[[150,30,10]]` mitten code — instance definitions

The smallest mitten code (Bhardwaj et al., *High-rate qLDPC processors*,
arXiv:2607.28795, Table I): the non-abelian lifted product LP(A,B) over
`𝔽₂[C₅×S₃]` with the Table XIII weight-3 sets, instantiating
`mittenChainComplex` (`Framework/Homological/LiftedProduct.lean`) at the
carrier `M150G = Multiplicative (ZMod 5) × DihedralGroup 3`.

Parameters `n = 150`, `k = 30` (both check matrices full rank),
`d = 10` (d_X = d_Z = 10, SAT-certified two ways in
`qec-lab:experiments/bb_lab/certificates/mitten_150_30_10_{X,Z}.cert.json`;
the Lean floors are the M4 stage of the attempt).

Element/set data and all offline-validated certificate tables live in the
generated `Data.lean`; this file adds the polynomial indicator functions
and the packaged complex.  Attempt state:
`qec-lab:pipeline/attempts/mitten_150_30_10/`.
-/

import QEC.Stabilizer.Codes.Mitten.M150.Data

namespace Quantum
namespace Stabilizer
namespace Homological
namespace LP
namespace M150

/-- `A = [a₀ a₁]` as indicator functions of the Table XIII sets. -/
def m150A : Fin 2 → M150G → ZMod 2 := fun α g =>
  if g ∈ (if α = 0 then a0 else a1) then 1 else 0

/-- `B = [b₀ b₁]` as indicator functions. -/
def m150B : Fin 2 → M150G → ZMod 2 := fun β g =>
  if g ∈ (if β = 0 then b0 else b1) then 1 else 0

/-- The `[[150,30,10]]` mitten chain complex over `C₅×S₃`. -/
noncomputable def m150Complex : HomologicalCode :=
  mittenChainComplex m150A m150B

lemma card_M150G : Fintype.card M150G = 30 := by decide

/-- The instance has 150 physical qubits. -/
lemma m150_numQubits : m150Complex.numQubits = 150 := by
  change lpNumQubits M150G = 150
  rw [lpNumQubits, card_M150G]

/-- Every base entry has weight 3 (check weight 9 = 3+3+3). -/
lemma sets_length :
    a0.length = 3 ∧ a1.length = 3 ∧ b0.length = 3 ∧ b1.length = 3 := by
  decide

/-- The paper's normalization: `a₁` and `b₁` contain the identity. -/
lemma one_mem_a1_b1 : (1 : M150G) ∈ a1 ∧ (1 : M150G) ∈ b1 := by decide

end M150
end LP
end Homological
end Stabilizer
end Quantum
