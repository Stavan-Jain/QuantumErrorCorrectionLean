import Mathlib.Tactic
import QEC.Stabilizer.Codes.ToricCodeN
import QEC.Stabilizer.Lattice.ToricLogicalCorrespondenceX
import QEC.Stabilizer.Lattice.ToricWrappingInvariants
import QEC.Stabilizer.PauliGroup.NQubitElement

namespace Quantum
namespace StabilizerGroup
namespace ToricCodeN

open scoped BigOperators
open NQubitPauliGroupElement

/-- Canonical horizontal noncontractible cycle used for the X-distance upper bound witness. -/
def horizontalLoopChain (L : ℕ) [Fact (0 < L)] : Stabilizer.Lattice.C1 L :=
  fun e =>
    match e with
    | Stabilizer.Lattice.EdgeIdx.h _ y =>
        if y = Stabilizer.Lattice.zeroCoord L then (1 : ZMod 2) else 0
    | Stabilizer.Lattice.EdgeIdx.v _ _ => 0

/-- X-type Pauli operator encoded by the canonical horizontal loop cycle. -/
def horizontalLoopXOperator (L : ℕ) [Fact (0 < L)] :
    NQubitPauliGroupElement (Stabilizer.Lattice.toricNumQubits L) :=
  Stabilizer.Lattice.toricXOperatorOfChain L (horizontalLoopChain L)

/-- X-distance predicate specialized to toric-code X-type logical operators. -/
def HasToricXDistance (L d : ℕ) [Fact (2 ≤ L)] : Prop :=
  d ≥ 1 ∧
  (∀ g : NQubitPauliGroupElement (numQubits L),
      NQubitPauliGroupElement.IsXTypeElement g →
      IsNontrivialLogicalOperator g (stabilizerGroup L) →
      0 < weight g →
      weight g ≥ d) ∧
  (∃ g : NQubitPauliGroupElement (numQubits L),
      NQubitPauliGroupElement.IsXTypeElement g ∧
      IsNontrivialLogicalOperator g (stabilizerGroup L) ∧
      weight g = d)

/-- Section-8 witness: the canonical horizontal loop is a toric 1-cycle. -/
theorem horizontalLoopChain_mem_toricCycles (L : ℕ) [Fact (2 ≤ L)] :
    horizontalLoopChain L ∈ Stabilizer.Lattice.toricCycles (L := L) := by
  sorry

/-- Section-8 witness: the canonical horizontal loop is not a toric 1-boundary. -/
theorem horizontalLoopChain_not_mem_toricBoundaries (L : ℕ) [Fact (2 ≤ L)] :
    horizontalLoopChain L ∉ Stabilizer.Lattice.toricBoundaries (L := L) := by
  sorry

/-- Section-8 witness: canonical horizontal loop chain has edge-weight `L`. -/
theorem horizontalLoopChain_edgeWeight_eq_L (L : ℕ) [Fact (2 ≤ L)] :
    Stabilizer.Lattice.edgeWeight (L := L) (horizontalLoopChain L) = L := by
  let z0 : Fin L := Stabilizer.Lattice.zeroCoord L
  let horizAtZero : Finset (Stabilizer.Lattice.EdgeIdx L) :=
    (Finset.univ.image (fun x : Fin L => Stabilizer.Lattice.EdgeIdx.h x z0))
  have hsupport :
      Stabilizer.Lattice.edgeSupport (L := L) (horizontalLoopChain L) = horizAtZero := by
    ext e
    constructor
    · intro he
      have hne : horizontalLoopChain L e ≠ 0 := by
        simpa [Stabilizer.Lattice.mem_edgeSupport] using he
      cases e with
      | h x y =>
          by_cases hy : y = z0
          · subst hy
            refine Finset.mem_image.mpr ?_
            exact ⟨x, Finset.mem_univ x, rfl⟩
          · have hy' : y = z0 := by
              simpa [horizontalLoopChain] using hne
            exact (hy hy').elim
      | v x y =>
          simp [horizontalLoopChain] at hne
    · intro he
      rcases Finset.mem_image.mp he with ⟨x, -, hx⟩
      subst hx
      simp [Stabilizer.Lattice.mem_edgeSupport, horizontalLoopChain, z0]
  have hinj : Function.Injective (fun x : Fin L => Stabilizer.Lattice.EdgeIdx.h x z0) := by
    intro a b h
    cases h
    rfl
  have hcard : horizAtZero.card = L := by
    calc
      horizAtZero.card
          = (Finset.univ.image (fun x : Fin L => Stabilizer.Lattice.EdgeIdx.h x z0)).card := rfl
      _ = (Finset.univ : Finset (Fin L)).card := by
        exact Finset.card_image_of_injective
          (s := (Finset.univ : Finset (Fin L)))
          (f := fun x : Fin L => Stabilizer.Lattice.EdgeIdx.h x z0)
          (by
            intro a b hab
            exact hinj hab)
      _ = L := by simp
  calc
    Stabilizer.Lattice.edgeWeight (L := L) (horizontalLoopChain L)
        = (Stabilizer.Lattice.edgeSupport (L := L) (horizontalLoopChain L)).card := rfl
    _ = horizAtZero.card := by rw [hsupport]
    _ = L := hcard

/-- Section-8 upper-bound witness packaged as a nontrivial X logical of weight `L`. -/
theorem exists_nontrivial_x_logical_weight_eq_L (L : ℕ) [Fact (2 ≤ L)] :
    ∃ g : NQubitPauliGroupElement (numQubits L),
      NQubitPauliGroupElement.IsXTypeElement g ∧
      IsNontrivialLogicalOperator g (stabilizerGroup L) ∧
      weight g = L := by
  sorry

/-- Section 8.1 scaffold: X-distance upper bound `dX ≤ L`. -/
theorem xDistance_upper_bound (L : ℕ) [Fact (2 ≤ L)] :
    ∃ g : NQubitPauliGroupElement (numQubits L),
      NQubitPauliGroupElement.IsXTypeElement g ∧
      IsNontrivialLogicalOperator g (stabilizerGroup L) ∧
      weight g ≤ L := by
  rcases exists_nontrivial_x_logical_weight_eq_L L with ⟨g, hgX, hgLogical, hgwt⟩
  refine ⟨g, hgX, hgLogical, ?_⟩
  simp [hgwt]

/-- Section 8.2 scaffold: any nontrivial X logical has weight at least `L`. -/
theorem nontrivial_x_logical_weight_ge_L (L : ℕ) [Fact (2 ≤ L)]
    (g : NQubitPauliGroupElement (numQubits L))
    (hgX : NQubitPauliGroupElement.IsXTypeElement g)
    (hgLogical : IsNontrivialLogicalOperator g (stabilizerGroup L)) :
    weight g ≥ L := by
  sorry

/-- Section 8 endpoint scaffold: the toric X-distance is `L`. -/
theorem toricCodeN_hasXDistance_L (L : ℕ) [Fact (2 ≤ L)] :
    HasToricXDistance L L := by
  refine ⟨?_, ?_, ?_⟩
  · have hL : 2 ≤ L := Fact.out
    omega
  · intro g hgX hgLogical hgPos
    exact nontrivial_x_logical_weight_ge_L L g hgX hgLogical
  · exact exists_nontrivial_x_logical_weight_eq_L L

/-- Section 8 endpoint alias: `dX = L` for the toric code. -/
theorem toricCodeN_dX_eq_L (L : ℕ) [Fact (2 ≤ L)] :
    HasToricXDistance L L := by
  simpa using toricCodeN_hasXDistance_L L

end ToricCodeN
end StabilizerGroup
end Quantum
