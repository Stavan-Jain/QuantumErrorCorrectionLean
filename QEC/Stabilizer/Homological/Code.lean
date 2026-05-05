import Mathlib.Tactic

/-!
# Abstract length-3 chain complex over `ZMod 2`

A `HomologicalCode` is a length-3 chain complex `C₂ →∂₂ C₁ →∂₁ C₀` over `𝔽₂`
with finite cells, satisfying the chain-complex law `∂₁ ∘ ∂₂ = 0`.  It is the
core data from which a CSS stabilizer code with `n = |C₁|` qubits and
`k = dim H₁` logical qubits is built.

This file sets up the abstract structure and the homology API:

* `HomologicalCode` (struct)
* `cycles`, `boundaries`, `H1`
* `boundaries_le_cycles`
* Rank-nullity for `∂₁` and `∂₂`
* `finrank_H1_eq_cycles_sub_boundaries`
* `cutMap` — the `𝔽₂`-transpose of `∂₁`, defined as a finite sum so that
  instance resolution stays cheap.

The CSS construction itself is in `QEC/Stabilizer/Homological/CSS.lean`.
-/

namespace Quantum
namespace Stabilizer
namespace Homological

open scoped BigOperators

/-- A length-3 chain complex over `ZMod 2` with finite, decidable cells.

`boundary1 ∘ boundary2 = 0` is the chain-complex law. -/
structure HomologicalCode where
  /-- Type of 0-cells (e.g. vertices). -/
  C0 : Type
  /-- Type of 1-cells (e.g. edges → physical qubits). -/
  C1 : Type
  /-- Type of 2-cells (e.g. faces). -/
  C2 : Type
  /-- Decidable equality on 0-cells. -/
  decEq0 : DecidableEq C0
  /-- Decidable equality on 1-cells. -/
  decEq1 : DecidableEq C1
  /-- Decidable equality on 2-cells. -/
  decEq2 : DecidableEq C2
  /-- Finitely many 0-cells. -/
  fin0 : Fintype C0
  /-- Finitely many 1-cells. -/
  fin1 : Fintype C1
  /-- Finitely many 2-cells. -/
  fin2 : Fintype C2
  /-- Boundary map `∂₁ : C₁ → C₀` (with chains as `ZMod 2`-valued functions). -/
  boundary1 : (C1 → ZMod 2) →ₗ[ZMod 2] (C0 → ZMod 2)
  /-- Boundary map `∂₂ : C₂ → C₁`. -/
  boundary2 : (C2 → ZMod 2) →ₗ[ZMod 2] (C1 → ZMod 2)
  /-- Chain-complex law: `∂₁ ∘ ∂₂ = 0`. -/
  boundary_comp : boundary1.comp boundary2 = 0
  /-- The number of physical qubits.  Each instance specifies this explicitly
  (e.g. the toric code uses `2 * L * L`); we relate it to `Fintype.card C₁`
  via `numQubits_eq` below.  Making this a field rather than a derived
  `abbrev` lets each instance use its own canonical Nat representation,
  which keeps the resulting `NQubitPauliGroupElement numQubits` type
  defeq to whatever the existing instance code uses. -/
  numQubits : ℕ
  /-- The number of qubits is `Fintype.card C₁`. -/
  numQubits_eq : @Fintype.card C1 fin1 = numQubits
  /-- A chosen bijection between 1-cells and qubit indices `Fin numQubits`.
  Each instance is free to choose its own qubit indexing — the toric instance
  uses `edgeToQubitIdx`, for example. -/
  edgeEquiv : C1 ≃ Fin numQubits

namespace HomologicalCode

attribute [instance] decEq0 decEq1 decEq2 fin0 fin1 fin2

variable (X : HomologicalCode)

/-- Pointwise form of the chain-complex law. -/
theorem boundary_comp_apply (f : X.C2 → ZMod 2) :
    X.boundary1 (X.boundary2 f) = 0 := by
  have h := congrArg (fun T => T f) X.boundary_comp
  simpa using h

/-- 1-cycles: `Z₁ = ker ∂₁`. -/
def cycles : Submodule (ZMod 2) (X.C1 → ZMod 2) :=
  LinearMap.ker X.boundary1

/-- 1-boundaries: `B₁ = im ∂₂`. -/
def boundaries : Submodule (ZMod 2) (X.C1 → ZMod 2) :=
  LinearMap.range X.boundary2

/-- Boundaries are cycles (`im ∂₂ ≤ ker ∂₁`). -/
theorem boundaries_le_cycles : X.boundaries ≤ X.cycles := by
  intro c hc
  rcases hc with ⟨f, rfl⟩
  exact X.boundary_comp_apply f

/-- `B₁` viewed as a submodule of `Z₁`. -/
abbrev boundarySubmoduleInCycles : Submodule (ZMod 2) X.cycles :=
  Submodule.comap X.cycles.subtype X.boundaries

/-- First homology `H₁ = Z₁ / B₁`. -/
abbrev H1 : Type :=
  X.cycles ⧸ X.boundarySubmoduleInCycles

/-- The `C₀` chain space has `Fintype.card C₀` dimensions. -/
theorem finrank_C0 :
    Module.finrank (ZMod 2) (X.C0 → ZMod 2) = Fintype.card X.C0 :=
  Module.finrank_fintype_fun_eq_card (R := ZMod 2) (η := X.C0)

/-- The `C₁` chain space has `Fintype.card C₁` dimensions. -/
theorem finrank_C1 :
    Module.finrank (ZMod 2) (X.C1 → ZMod 2) = Fintype.card X.C1 :=
  Module.finrank_fintype_fun_eq_card (R := ZMod 2) (η := X.C1)

/-- The `C₂` chain space has `Fintype.card C₂` dimensions. -/
theorem finrank_C2 :
    Module.finrank (ZMod 2) (X.C2 → ZMod 2) = Fintype.card X.C2 :=
  Module.finrank_fintype_fun_eq_card (R := ZMod 2) (η := X.C2)

/-- Rank-nullity for `∂₁`: `dim C₁ = dim Z₁ + rank ∂₁`. -/
theorem rank_nullity_boundary1 :
    Module.finrank (ZMod 2) (X.C1 → ZMod 2) =
      Module.finrank (ZMod 2) X.cycles +
        Module.finrank (ZMod 2) (LinearMap.range X.boundary1) := by
  simpa [cycles, add_comm] using
    (LinearMap.finrank_range_add_finrank_ker X.boundary1).symm

/-- Rank-nullity for `∂₂`: `dim C₂ = dim (ker ∂₂) + dim B₁`. -/
theorem rank_nullity_boundary2 :
    Module.finrank (ZMod 2) (X.C2 → ZMod 2) =
      Module.finrank (ZMod 2) (LinearMap.ker X.boundary2) +
        Module.finrank (ZMod 2) X.boundaries := by
  simpa [boundaries, add_comm] using
    (LinearMap.finrank_range_add_finrank_ker X.boundary2).symm

/-- The quotient bridge `dim H₁ = dim Z₁ - dim B₁`. -/
theorem finrank_H1_eq_cycles_sub_boundaries :
    @Module.finrank (ZMod 2) X.H1 _
      (Submodule.Quotient.addCommGroup
        (X.boundarySubmoduleInCycles)).toAddCommMonoid
      (Submodule.Quotient.module X.boundarySubmoduleInCycles) =
      Module.finrank (ZMod 2) X.cycles -
        Module.finrank (ZMod 2) X.boundaries := by
  have hquot :
      @Module.finrank (ZMod 2) X.H1 _
          (Submodule.Quotient.addCommGroup
            X.boundarySubmoduleInCycles).toAddCommMonoid
          (Submodule.Quotient.module X.boundarySubmoduleInCycles) +
          Module.finrank (ZMod 2) X.boundarySubmoduleInCycles =
        Module.finrank (ZMod 2) X.cycles := by
    simpa [H1, boundarySubmoduleInCycles] using
      (Submodule.finrank_quotient_add_finrank (R := ZMod 2)
        X.boundarySubmoduleInCycles)
  have hcomap :
      Module.finrank (ZMod 2) X.boundarySubmoduleInCycles =
        Module.finrank (ZMod 2) X.boundaries := by
    simpa [boundarySubmoduleInCycles] using
      (Submodule.comapSubtypeEquivOfLe X.boundaries_le_cycles).finrank_eq
  rw [hcomap] at hquot
  exact Nat.eq_sub_of_add_eq hquot

/-- The `𝔽₂`-transpose of `∂₁`, written as a finite sum.

`(cutMap s) e = ∑ v, s v · ∂₁(δ_e)(v)` where `δ_e := Pi.single e 1`.

This is what one would get from `LinearMap.dualMap`, but inlined as a finite
sum to keep instance synthesis cheap (no `Module.Dual` lookups). -/
noncomputable def cutMap : (X.C0 → ZMod 2) →ₗ[ZMod 2] (X.C1 → ZMod 2) where
  toFun s := fun e => ∑ v : X.C0, s v * X.boundary1 (Pi.single e 1) v
  map_add' s t := by
    ext e
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' a s := by
    ext e
    simp [Finset.mul_sum, mul_assoc]

@[simp] theorem cutMap_apply (s : X.C0 → ZMod 2) (e : X.C1) :
    X.cutMap s e = ∑ v : X.C0, s v * X.boundary1 (Pi.single e 1) v := rfl

/-- Symmetric pairing form of the transpose property.

`⟨∂₁ c, s⟩ = ⟨c, cutMap s⟩` over `𝔽₂` with the standard pairing
`⟨a, b⟩ = ∑ x, a x · b x`. -/
theorem boundary1_cutMap_transpose (c : X.C1 → ZMod 2) (s : X.C0 → ZMod 2) :
    ∑ v : X.C0, X.boundary1 c v * s v =
      ∑ e : X.C1, c e * X.cutMap s e := by
  -- Expand `c = ∑ e, c e • Pi.single e 1` and push the sum through `boundary1`.
  have hc : c = ∑ e : X.C1, c e • (Pi.single e (1 : ZMod 2)) := by
    ext e
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hc]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [cutMap_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  ring

end HomologicalCode

end Homological
end Stabilizer
end Quantum
