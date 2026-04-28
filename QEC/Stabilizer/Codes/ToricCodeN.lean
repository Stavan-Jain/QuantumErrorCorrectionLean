import Mathlib.Tactic
import Mathlib.Data.List.OfFn
import QEC.Stabilizer.Core.StabilizerGroup
import QEC.Stabilizer.Core.SubgroupLemmas
import QEC.Stabilizer.Core.CSSNoNegI
import QEC.Stabilizer.Core.Centralizer
import QEC.Stabilizer.PauliGroup.Commutation
import QEC.Stabilizer.PauliGroup.CommutationTactics
import QEC.Stabilizer.PauliGroup.SupportLemmas
import QEC.Stabilizer.BinarySymplectic.Core
import QEC.Stabilizer.BinarySymplectic.CheckMatrix
import QEC.Stabilizer.BinarySymplectic.CheckMatrixDecidable
import QEC.Stabilizer.BinarySymplectic.SymplecticSpan
import QEC.Stabilizer.Core.StabilizerCode
import QEC.Stabilizer.Core.GeneratorListLemmas
import QEC.Stabilizer.Core.CSSCommutationLemmas
import QEC.Stabilizer.BinarySymplectic.IndependentEquiv
import QEC.Stabilizer.BinarySymplectic.SymplecticInner
import QEC.Stabilizer.PauliGroup.NQubitOperator
import QEC.Stabilizer.Lattice.FinPeriodic
import QEC.Stabilizer.Lattice.GridIndexing
import QEC.Stabilizer.Lattice.ToricHomology
import QEC.Stabilizer.Codes.ToricCode8

/-!
# Parametric toric code on an L×L torus

Formalizes the parametric toric code for an L×L lattice:
- `numQubits L = 2·L·L` physical qubits placed on edges
- Horizontal edges `H(x,y)` and vertical edges `V(x,y)` with periodic boundaries
- Face stabilizers (X-type) and vertex stabilizers (Z-type)
- All generators as lists for use in Steps 2–4

Convention note: this file uses face=X and vertex=Z checks, matching the convention
in `distance_proof.md`. Some expositions use the swapped convention (face=Z, vertex=X);
both are equivalent via global Hadamard (X ↔ Z on every qubit).

Step 1: qubit–edge bijection, generator definitions, and consistency check at L=2
against the concrete `ToricCode8`.
-/

namespace Quantum
open scoped BigOperators

namespace StabilizerGroup
namespace ToricCodeN

open NQubitPauliGroupElement

/-!
## 1. Qubit count and edge bijection
-/

/-- Physical qubit count for an L×L toric code. -/
abbrev numQubits (L : ℕ) : ℕ := 2 * L * L

/-- Horizontal edge H(x,y): qubit index `y·L + x` (range 0..L²-1). -/
def hEdge (L : ℕ) (x y : Fin L) : Fin (numQubits L) :=
  ⟨y.val * L + x.val, by simp only [numQubits]; have := x.isLt; have := y.isLt; nlinarith⟩

/-- Vertical edge V(x,y): qubit index `L² + y·L + x` (range L²..2L²-1). -/
def vEdge (L : ℕ) (x y : Fin L) : Fin (numQubits L) :=
  ⟨L * L + y.val * L + x.val, by simp only [numQubits]; have := x.isLt; have := y.isLt; nlinarith⟩

@[simp] lemma hEdge_val (L : ℕ) (x y : Fin L) :
    (hEdge L x y).val = y.val * L + x.val := rfl

@[simp] lemma vEdge_val (L : ℕ) (x y : Fin L) :
    (vEdge L x y).val = L * L + y.val * L + x.val := rfl

/-- H-edge indices are strictly less than L², V-edge indices are at least L². -/
lemma hEdge_val_lt_sq (L : ℕ) (x y : Fin L) : (hEdge L x y).val < L * L := by
  simp only [hEdge_val]; have := x.isLt; have := y.isLt; nlinarith

lemma vEdge_val_ge_sq (L : ℕ) (x y : Fin L) : L * L ≤ (vEdge L x y).val := by
  simp only [vEdge_val]; omega

/-- Horizontal edge indexing as a map from lattice coordinates is injective. -/
lemma hEdge_injective (L : ℕ) [Fact (0 < L)] :
    Function.Injective (fun p : Fin L × Fin L => hEdge L p.1 p.2) := by
  intro p q h
  apply Stabilizer.Lattice.rowMajor_injective (L := L)
  exact congrArg Fin.val h

/-- Vertical edge indexing as a map from lattice coordinates is injective. -/
lemma vEdge_injective (L : ℕ) [Fact (0 < L)] :
    Function.Injective (fun p : Fin L × Fin L => vEdge L p.1 p.2) := by
  intro p q h
  have hsum : p.2.val * L + p.1.val = q.2.val * L + q.1.val := by
    have hval : (vEdge L p.1 p.2).val = (vEdge L q.1 q.2).val := congrArg Fin.val h
    have hval' : L * L + (p.2.val * L + p.1.val) = L * L + (q.2.val * L + q.1.val) := by
      simpa [vEdge_val, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hval
    exact Nat.add_left_cancel hval'
  apply Stabilizer.Lattice.rowMajor_injective (L := L)
  exact hsum

/-- Characterization of equality for horizontal edge indices. -/
lemma hEdge_eq_iff (L : ℕ) [Fact (0 < L)] (x₁ y₁ x₂ y₂ : Fin L) :
    hEdge L x₁ y₁ = hEdge L x₂ y₂ ↔ x₁ = x₂ ∧ y₁ = y₂ := by
  constructor
  · intro h
    have hinj := hEdge_injective (L := L)
    have hp : (x₁, y₁) = (x₂, y₂) := hinj h
    cases hp
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Characterization of equality for vertical edge indices. -/
lemma vEdge_eq_iff (L : ℕ) [Fact (0 < L)] (x₁ y₁ x₂ y₂ : Fin L) :
    vEdge L x₁ y₁ = vEdge L x₂ y₂ ↔ x₁ = x₂ ∧ y₁ = y₂ := by
  constructor
  · intro h
    have hinj := vEdge_injective (L := L)
    have hp : (x₁, y₁) = (x₂, y₂) := hinj h
    cases hp
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Horizontal and vertical edge encodings are disjoint. -/
lemma hEdge_ne_vEdge (L : ℕ) (x₁ y₁ x₂ y₂ : Fin L) :
    hEdge L x₁ y₁ ≠ vEdge L x₂ y₂ := by
  exact Stabilizer.Lattice.fin_ne_of_val_lt_offset_le
    (hEdge_val_lt_sq L x₁ y₁) (vEdge_val_ge_sq L x₂ y₂)

/-!
## 2. Periodic coordinate helpers
-/

/-- Successor modulo `L` on coordinates. -/
abbrev next (L : ℕ) [Fact (0 < L)] (i : Fin L) : Fin L := Stabilizer.Lattice.next L i

/-- Predecessor modulo `L` on coordinates. -/
abbrev prev (L : ℕ) [Fact (0 < L)] (i : Fin L) : Fin L := Stabilizer.Lattice.prev L i

/-!
## 3. Parametric toric stabilizer generators
-/

/-- Vertex stabilizer at `(x,y)`: Z on the four incident edges. -/
def vertexStab (L : ℕ) [Fact (0 < L)] (x y : Fin L) : NQubitPauliGroupElement (numQubits L) :=
  ⟨0, (((NQubitPauliOperator.identity (numQubits L)).set (hEdge L x y) PauliOperator.Z
    |>.set (hEdge L (prev L x) y) PauliOperator.Z
    |>.set (vEdge L x y) PauliOperator.Z)
    |>.set (vEdge L x (prev L y)) PauliOperator.Z)⟩

/-- Face stabilizer at `(x,y)`: X on the four boundary edges. -/
def faceStab (L : ℕ) [Fact (0 < L)] (x y : Fin L) : NQubitPauliGroupElement (numQubits L) :=
  ⟨0, (((NQubitPauliOperator.identity (numQubits L)).set (hEdge L x y) PauliOperator.X
    |>.set (hEdge L x (next L y)) PauliOperator.X
    |>.set (vEdge L x y) PauliOperator.X)
    |>.set (vEdge L (next L x) y) PauliOperator.X)⟩

/-- X-type generator family indexed by faces. -/
def XGenerators (L : ℕ) [Fact (0 < L)] : Set (NQubitPauliGroupElement (numQubits L)) :=
  Set.range (fun p : Fin L × Fin L => faceStab L p.1 p.2)

/-- Z-type generator family indexed by vertices. -/
def ZGenerators (L : ℕ) [Fact (0 < L)] : Set (NQubitPauliGroupElement (numQubits L)) :=
  Set.range (fun p : Fin L × Fin L => vertexStab L p.1 p.2)

/-- Full toric generator set. -/
def generators (L : ℕ) [Fact (0 < L)] : Set (NQubitPauliGroupElement (numQubits L)) :=
  ZGenerators L ∪ XGenerators L

/-- All lattice coordinates `(x,y)` as a canonical list. -/
def coords (L : ℕ) : List (Fin L × Fin L) :=
  (List.finRange L).product (List.finRange L)

/-- Every coordinate pair appears in `coords L`. -/
lemma mem_coords (L : ℕ) (p : Fin L × Fin L) : p ∈ coords L := by
  simpa [coords] using GeneratorListLemmas.mem_finRange_product L p

/-- Z generators as a canonical list. -/
def generatorsListZ (L : ℕ) [Fact (0 < L)] : List (NQubitPauliGroupElement (numQubits L)) :=
  (coords L).map (fun p => vertexStab L p.1 p.2)

/-- X generators as a canonical list. -/
def generatorsListX (L : ℕ) [Fact (0 < L)] : List (NQubitPauliGroupElement (numQubits L)) :=
  (coords L).map (fun p => faceStab L p.1 p.2)

/-- Full generator list (all Z generators then all X generators). -/
def generatorsList (L : ℕ) [Fact (0 < L)] : List (NQubitPauliGroupElement (numQubits L)) :=
  generatorsListZ L ++ generatorsListX L

/-- The Z-generator list has exactly the Z-generator set as elements. -/
lemma listToSet_generatorsListZ (L : ℕ) [Fact (0 < L)] :
    NQubitPauliGroupElement.listToSet (generatorsListZ L) = ZGenerators L := by
  simpa [generatorsListZ, coords, ZGenerators] using
    (GeneratorListLemmas.listToSet_map_product_finRange_eq_range
      (n := numQubits L) (L := L) (f := fun p => vertexStab L p.1 p.2))

/-- The X-generator list has exactly the X-generator set as elements. -/
lemma listToSet_generatorsListX (L : ℕ) [Fact (0 < L)] :
    NQubitPauliGroupElement.listToSet (generatorsListX L) = XGenerators L := by
  simpa [generatorsListX, coords, XGenerators] using
    (GeneratorListLemmas.listToSet_map_product_finRange_eq_range
      (n := numQubits L) (L := L) (f := fun p => faceStab L p.1 p.2))

/-- The full generator list has exactly the union generator set as elements. -/
lemma listToSet_generatorsList (L : ℕ) [Fact (0 < L)] :
    NQubitPauliGroupElement.listToSet (generatorsList L) = generators L := by
  ext g
  constructor
  · intro hg
    have h' : g ∈ NQubitPauliGroupElement.listToSet (generatorsListZ L) ∨
        g ∈ NQubitPauliGroupElement.listToSet (generatorsListX L) := by
      simpa [generatorsList, NQubitPauliGroupElement.listToSet] using hg
    rcases h' with hgZ | hgX
    · exact Or.inl (by rwa [listToSet_generatorsListZ] at hgZ)
    · exact Or.inr (by rwa [listToSet_generatorsListX] at hgX)
  · intro hg
    rcases hg with hgZ | hgX
    · have hgZ' : g ∈ NQubitPauliGroupElement.listToSet (generatorsListZ L) := by
        rwa [listToSet_generatorsListZ]
      simpa [generatorsList, NQubitPauliGroupElement.listToSet] using Or.inl hgZ'
    · have hgX' : g ∈ NQubitPauliGroupElement.listToSet (generatorsListX L) := by
        rwa [listToSet_generatorsListX]
      simpa [generatorsList, NQubitPauliGroupElement.listToSet] using Or.inr hgX'

/-!
## 4. CSS typing and commutation
-/

/-- Any two Z-type elements commute. -/
private lemma ZType_commutes {n : ℕ} {g h : NQubitPauliGroupElement n}
    (hg : NQubitPauliGroupElement.IsZTypeElement g)
    (hh : NQubitPauliGroupElement.IsZTypeElement h) :
    g * h = h * g := by
  exact CSSCommutationLemmas.ZType_commutes hg hh

/-- Any two X-type elements commute. -/
private lemma XType_commutes {n : ℕ} {g h : NQubitPauliGroupElement n}
    (hg : NQubitPauliGroupElement.IsXTypeElement g)
    (hh : NQubitPauliGroupElement.IsXTypeElement h) :
    g * h = h * g := by
  exact CSSCommutationLemmas.XType_commutes hg hh

/-- Every face stabilizer is X-type. -/
lemma faceStab_is_XType (L : ℕ) [Fact (0 < L)] (x y : Fin L) :
    NQubitPauliGroupElement.IsXTypeElement (faceStab L x y) := by
  refine ⟨rfl, ?_⟩
  let op0 : NQubitPauliOperator (numQubits L) := NQubitPauliOperator.identity (numQubits L)
  let op1 : NQubitPauliOperator (numQubits L) := op0.set (hEdge L x y) PauliOperator.X
  let op2 : NQubitPauliOperator (numQubits L) := op1.set (hEdge L x (next L y)) PauliOperator.X
  let op3 : NQubitPauliOperator (numQubits L) := op2.set (vEdge L x y) PauliOperator.X
  let op4 : NQubitPauliOperator (numQubits L) := op3.set (vEdge L (next L x) y) PauliOperator.X
  have h0 : NQubitPauliOperator.IsXType op0 := by
    simpa [op0] using (NQubitPauliOperator.IsXType_identity (n := numQubits L))
  have h1 : NQubitPauliOperator.IsXType op1 := by
    simpa [op1] using NQubitPauliOperator.IsXType_set_X_of_IsXType op0 (hEdge L x y) h0
  have h2 : NQubitPauliOperator.IsXType op2 := by
    simpa [op2] using NQubitPauliOperator.IsXType_set_X_of_IsXType op1 (hEdge L x (next L y)) h1
  have h3 : NQubitPauliOperator.IsXType op3 := by
    simpa [op3] using NQubitPauliOperator.IsXType_set_X_of_IsXType op2 (vEdge L x y) h2
  have h4 : NQubitPauliOperator.IsXType op4 := by
    simpa [op4] using NQubitPauliOperator.IsXType_set_X_of_IsXType op3 (vEdge L (next L x) y) h3
  simpa [faceStab, op0, op1, op2, op3, op4] using h4

/-- Every vertex stabilizer is Z-type. -/
lemma vertexStab_is_ZType (L : ℕ) [Fact (0 < L)] (x y : Fin L) :
    NQubitPauliGroupElement.IsZTypeElement (vertexStab L x y) := by
  refine ⟨rfl, ?_⟩
  let op0 : NQubitPauliOperator (numQubits L) := NQubitPauliOperator.identity (numQubits L)
  let op1 : NQubitPauliOperator (numQubits L) := op0.set (hEdge L x y) PauliOperator.Z
  let op2 : NQubitPauliOperator (numQubits L) := op1.set (hEdge L (prev L x) y) PauliOperator.Z
  let op3 : NQubitPauliOperator (numQubits L) := op2.set (vEdge L x y) PauliOperator.Z
  let op4 : NQubitPauliOperator (numQubits L) := op3.set (vEdge L x (prev L y)) PauliOperator.Z
  have h0 : NQubitPauliOperator.IsZType op0 := by
    simpa [op0] using (NQubitPauliOperator.IsZType_identity (n := numQubits L))
  have h1 : NQubitPauliOperator.IsZType op1 := by
    simpa [op1] using NQubitPauliOperator.IsZType_set_Z_of_IsZType op0 (hEdge L x y) h0
  have h2 : NQubitPauliOperator.IsZType op2 := by
    simpa [op2] using NQubitPauliOperator.IsZType_set_Z_of_IsZType op1 (hEdge L (prev L x) y) h1
  have h3 : NQubitPauliOperator.IsZType op3 := by
    simpa [op3] using NQubitPauliOperator.IsZType_set_Z_of_IsZType op2 (vEdge L x y) h2
  have h4 : NQubitPauliOperator.IsZType op4 := by
    simpa [op4] using NQubitPauliOperator.IsZType_set_Z_of_IsZType op3 (vEdge L x (prev L y)) h3
  simpa [vertexStab, op0, op1, op2, op3, op4] using h4

/-- All Z generators are Z-type. -/
lemma ZGenerators_are_ZType (L : ℕ) [Fact (0 < L)] :
    ∀ g, g ∈ ZGenerators L → NQubitPauliGroupElement.IsZTypeElement g := by
  intro g hg
  rcases hg with ⟨⟨x, y⟩, rfl⟩
  exact vertexStab_is_ZType L x y

/-- All X generators are X-type. -/
lemma XGenerators_are_XType (L : ℕ) [Fact (0 < L)] :
    ∀ g, g ∈ XGenerators L → NQubitPauliGroupElement.IsXTypeElement g := by
  intro g hg
  rcases hg with ⟨⟨x, y⟩, rfl⟩
  exact faceStab_is_XType L x y

/-- Any two Z generators commute. -/
lemma ZGenerators_commute (L : ℕ) [Fact (0 < L)] :
    ∀ z₁ ∈ ZGenerators L, ∀ z₂ ∈ ZGenerators L, z₁ * z₂ = z₂ * z₁ := by
  intro z₁ hz₁ z₂ hz₂
  exact ZType_commutes (ZGenerators_are_ZType L z₁ hz₁) (ZGenerators_are_ZType L z₂ hz₂)

/-- Any two X generators commute. -/
lemma XGenerators_commute (L : ℕ) [Fact (0 < L)] :
    ∀ x₁ ∈ XGenerators L, ∀ x₂ ∈ XGenerators L, x₁ * x₂ = x₂ * x₁ := by
  intro x₁ hx₁ x₂ hx₂
  exact XType_commutes (XGenerators_are_XType L x₁ hx₁) (XGenerators_are_XType L x₂ hx₂)

/-- Support characterization for a face stabilizer. -/
lemma mem_support_faceStab_iff (L : ℕ) [Fact (0 < L)] (xf yf : Fin L) (i : Fin (numQubits L)) :
    i ∈ (faceStab L xf yf).operators.support ↔
      i = hEdge L xf yf ∨ i = hEdge L xf (next L yf) ∨
      i = vEdge L xf yf ∨ i = vEdge L (next L xf) yf := by
  constructor
  · intro hi
    by_contra hnot
    have hi' : (faceStab L xf yf).operators i ≠ PauliOperator.I := by
      simpa [NQubitPauliOperator.support] using hi
    have h1 : i ≠ hEdge L xf yf := by intro h; exact hnot (Or.inl h)
    have h2 : i ≠ hEdge L xf (next L yf) := by
      intro h
      exact hnot (Or.inr (Or.inl h))
    have h3 : i ≠ vEdge L xf yf := by
      intro h
      exact hnot (Or.inr (Or.inr (Or.inl h)))
    have h4 : i ≠ vEdge L (next L xf) yf := by
      intro h
      exact hnot (Or.inr (Or.inr (Or.inr h)))
    have hI : (faceStab L xf yf).operators i = PauliOperator.I := by
      simp [faceStab, NQubitPauliOperator.set, NQubitPauliOperator.identity, h1, h2, h3, h4]
    exact hi' hI
  · intro hi
    rcases hi with h1 | h2 | h3 | h4
    · subst h1
      simp [NQubitPauliOperator.support, faceStab, NQubitPauliOperator.set]
    · subst h2
      simp [NQubitPauliOperator.support, faceStab, NQubitPauliOperator.set]
    · subst h3
      simp [NQubitPauliOperator.support, faceStab, NQubitPauliOperator.set]
    · subst h4
      simp [NQubitPauliOperator.support, faceStab, NQubitPauliOperator.set]

/-- Support characterization for a vertex stabilizer. -/
lemma mem_support_vertexStab_iff (L : ℕ) [Fact (0 < L)] (xv yv : Fin L) (i : Fin (numQubits L)) :
    i ∈ (vertexStab L xv yv).operators.support ↔
      i = hEdge L xv yv ∨ i = hEdge L (prev L xv) yv ∨
      i = vEdge L xv yv ∨ i = vEdge L xv (prev L yv) := by
  constructor
  · intro hi
    by_contra hnot
    have hi' : (vertexStab L xv yv).operators i ≠ PauliOperator.I := by
      simpa [NQubitPauliOperator.support] using hi
    have h1 : i ≠ hEdge L xv yv := by intro h; exact hnot (Or.inl h)
    have h2 : i ≠ hEdge L (prev L xv) yv := by
      intro h
      exact hnot (Or.inr (Or.inl h))
    have h3 : i ≠ vEdge L xv yv := by
      intro h
      exact hnot (Or.inr (Or.inr (Or.inl h)))
    have h4 : i ≠ vEdge L xv (prev L yv) := by
      intro h
      exact hnot (Or.inr (Or.inr (Or.inr h)))
    have hI : (vertexStab L xv yv).operators i = PauliOperator.I := by
      simp [vertexStab, NQubitPauliOperator.set, NQubitPauliOperator.identity, h1, h2, h3, h4]
    exact hi' hI
  · intro hi
    rcases hi with h1 | h2 | h3 | h4
    · subst h1
      simp [NQubitPauliOperator.support, vertexStab, NQubitPauliOperator.set]
    · subst h2
      simp [NQubitPauliOperator.support, vertexStab, NQubitPauliOperator.set]
    · subst h3
      simp [NQubitPauliOperator.support, vertexStab, NQubitPauliOperator.set]
    · subst h4
      simp [NQubitPauliOperator.support, vertexStab, NQubitPauliOperator.set]

/-- At each qubit, face/vertex anticommute exactly when both supports contain that qubit. -/
lemma anticommutesAt_face_vertex_iff_mem_support_both
    (L : ℕ) [Fact (0 < L)] (xf yf xv yv : Fin L) (i : Fin (numQubits L)) :
    NQubitPauliGroupElement.anticommutesAt
      (faceStab L xf yf).operators (vertexStab L xv yv).operators i
      ↔ i ∈ (faceStab L xf yf).operators.support ∧ i ∈ (vertexStab L xv yv).operators.support := by
  exact NQubitPauliGroupElement.anticommutesAt_iff_mem_support_both_of_XZType
    (faceStab_is_XType L xf yf).2 (vertexStab_is_ZType L xv yv).2 i

/-- Any Z generator commutes with any X generator. -/
lemma ZGenerators_commute_XGenerators (L : ℕ) [Fact (2 ≤ L)] :
    ∀ z ∈ ZGenerators L, ∀ x ∈ XGenerators L, z * x = x * z := by
  classical
  intro z hz x hx
  rcases hz with ⟨⟨xv, yv⟩, rfl⟩
  rcases hx with ⟨⟨xf, yf⟩, rfl⟩
  haveI : Fact (0 < L) := ⟨Nat.lt_of_lt_of_le (by decide : 0 < 2) (Fact.out : 2 ≤ L)⟩
  let C : Prop := (xv = xf ∨ xv = next L xf) ∧ (yv = yf ∨ yv = next L yf)
  let hh : Fin (numQubits L) := hEdge L xf yv
  let vv : Fin (numQubits L) := vEdge L xv yf
  have hboth :
      ∀ i : Fin (numQubits L),
        i ∈ (faceStab L xf yf).operators.support ∧ i ∈ (vertexStab L xv yv).operators.support
          ↔ C ∧ (i = hh ∨ i = vv) := by
    intro i
    constructor
    · intro hi
      rcases (mem_support_faceStab_iff L xf yf i).1 hi.1 with hf | hf | hf | hf
      · rcases (mem_support_vertexStab_iff L xv yv i).1 hi.2 with hv | hv | hv | hv
        · have hEq : hEdge L xv yv = hEdge L xf yf := hv.symm.trans hf
          rcases (hEdge_eq_iff L xv yv xf yf).1 hEq with ⟨hxEq, hyEq⟩
          refine ⟨?_, Or.inl ?_⟩
          · exact ⟨Or.inl hxEq, Or.inl hyEq⟩
          · subst hxEq hyEq
            simpa [hh] using hf
        · have hEq : hEdge L (prev L xv) yv = hEdge L xf yf := hv.symm.trans hf
          rcases (hEdge_eq_iff L (prev L xv) yv xf yf).1 hEq with ⟨hxPrev, hyEq⟩
          refine ⟨?_, Or.inl ?_⟩
          · exact ⟨Or.inr ((Stabilizer.Lattice.prev_eq_iff_eq_next L xv xf).1 hxPrev), Or.inl hyEq⟩
          · subst hyEq
            simpa [hh] using hf
        · exact False.elim ((hEdge_ne_vEdge L xf yf xv yv) (hf.symm.trans hv))
        · exact False.elim ((hEdge_ne_vEdge L xf yf xv (prev L yv)) (hf.symm.trans hv))
      · rcases (mem_support_vertexStab_iff L xv yv i).1 hi.2 with hv | hv | hv | hv
        · have hEq : hEdge L xv yv = hEdge L xf (next L yf) := hv.symm.trans hf
          rcases (hEdge_eq_iff L xv yv xf (next L yf)).1 hEq with ⟨hxEq, hyEq⟩
          refine ⟨?_, Or.inl ?_⟩
          · exact ⟨Or.inl hxEq, Or.inr hyEq⟩
          · subst hxEq hyEq
            simpa [hh] using hf
        · have hEq : hEdge L (prev L xv) yv = hEdge L xf (next L yf) := hv.symm.trans hf
          rcases (hEdge_eq_iff L (prev L xv) yv xf (next L yf)).1 hEq with ⟨hxPrev, hyEq⟩
          refine ⟨?_, Or.inl ?_⟩
          · exact
              ⟨Or.inr ((Stabilizer.Lattice.prev_eq_iff_eq_next L xv xf).1 hxPrev), Or.inr hyEq⟩
          · subst hyEq
            simpa [hh] using hf
        · exact False.elim ((hEdge_ne_vEdge L xf (next L yf) xv yv) (hf.symm.trans hv))
        · exact
            False.elim ((hEdge_ne_vEdge L xf (next L yf) xv (prev L yv)) (hf.symm.trans hv))
      · rcases (mem_support_vertexStab_iff L xv yv i).1 hi.2 with hv | hv | hv | hv
        · exact False.elim ((hEdge_ne_vEdge L xv yv xf yf) (hv.symm.trans hf))
        · exact False.elim ((hEdge_ne_vEdge L (prev L xv) yv xf yf) (hv.symm.trans hf))
        · have hEq : vEdge L xv yv = vEdge L xf yf := hv.symm.trans hf
          rcases (vEdge_eq_iff L xv yv xf yf).1 hEq with ⟨hxEq, hyEq⟩
          refine ⟨?_, Or.inr ?_⟩
          · exact ⟨Or.inl hxEq, Or.inl hyEq⟩
          · subst hxEq hyEq
            simpa [vv] using hf
        · have hEq : vEdge L xv (prev L yv) = vEdge L xf yf := hv.symm.trans hf
          rcases (vEdge_eq_iff L xv (prev L yv) xf yf).1 hEq with ⟨hxEq, hyPrev⟩
          refine ⟨?_, Or.inr ?_⟩
          · exact ⟨Or.inl hxEq, Or.inr ((Stabilizer.Lattice.prev_eq_iff_eq_next L yv yf).1 hyPrev)⟩
          · subst hxEq hyPrev
            simpa [vv] using hf
      · rcases (mem_support_vertexStab_iff L xv yv i).1 hi.2 with hv | hv | hv | hv
        · exact False.elim ((hEdge_ne_vEdge L xv yv (next L xf) yf) (hv.symm.trans hf))
        · exact
            False.elim ((hEdge_ne_vEdge L (prev L xv) yv (next L xf) yf) (hv.symm.trans hf))
        · have hEq : vEdge L xv yv = vEdge L (next L xf) yf := hv.symm.trans hf
          rcases (vEdge_eq_iff L xv yv (next L xf) yf).1 hEq with ⟨hxEq, hyEq⟩
          refine ⟨?_, Or.inr ?_⟩
          · exact ⟨Or.inr hxEq, Or.inl hyEq⟩
          · subst hxEq hyEq
            simpa [vv] using hf
        · have hEq : vEdge L xv (prev L yv) = vEdge L (next L xf) yf := hv.symm.trans hf
          rcases (vEdge_eq_iff L xv (prev L yv) (next L xf) yf).1 hEq with ⟨hxEq, hyPrev⟩
          refine ⟨?_, Or.inr ?_⟩
          · exact ⟨Or.inr hxEq, Or.inr ((Stabilizer.Lattice.prev_eq_iff_eq_next L yv yf).1 hyPrev)⟩
          · subst hxEq hyPrev
            simpa [vv] using hf
    · rintro ⟨hC, hi⟩
      rcases hC with ⟨hxC, hyC⟩
      rcases hi with hi | hi
      · subst hi
        constructor
        · rw [mem_support_faceStab_iff L xf yf]
          rcases hyC with rfl | hyNext
          · exact Or.inl rfl
          · exact Or.inr (Or.inl (by simp [hh, hyNext]))
        · rw [mem_support_vertexStab_iff L xv yv]
          rcases hxC with hxEq | hxNext
          · exact Or.inl (by simp [hh, hxEq])
          · have hPrev : prev L xv = xf := by
              rw [hxNext]
              simp [Stabilizer.Lattice.prev_next]
            exact Or.inr (Or.inl (by simp [hh, hPrev]))
      · subst hi
        constructor
        · rw [mem_support_faceStab_iff L xf yf]
          rcases hxC with hxEq | hxNext
          · exact Or.inr (Or.inr (Or.inl (by simp [vv, hxEq])))
          · exact Or.inr (Or.inr (Or.inr (by simp [vv, hxNext])))
        · rw [mem_support_vertexStab_iff L xv yv]
          rcases hyC with hyEq | hyNext
          · exact Or.inr (Or.inr (Or.inl (by simp [vv, hyEq])))
          · have hPrev : prev L yv = yf := by
              rw [hyNext]
              simp [Stabilizer.Lattice.prev_next]
            exact Or.inr (Or.inr (Or.inr (by simp [vv, hPrev])))
  pauli_comm_even_anticommutes
  by_cases hC : C
  · have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt
              (vertexStab L xv yv).operators (faceStab L xf yf).operators)) =
        ({hh, vv} : Finset (Fin (numQubits L))) := by
      ext i
      constructor
      · intro hi
        have hanti : C ∧ (i = hh ∨ i = vv) := by
          have hi' :
              NQubitPauliGroupElement.anticommutesAt
                (vertexStab L xv yv).operators (faceStab L xf yf).operators i :=
            (Finset.mem_filter.mp hi).2
          have hi'' :
              i ∈ (faceStab L xf yf).operators.support ∧
                i ∈ (vertexStab L xv yv).operators.support := by
            have hiZX :
                i ∈ (vertexStab L xv yv).operators.support ∧
                  i ∈ (faceStab L xf yf).operators.support := by
              exact (NQubitPauliGroupElement.anticommutesAt_iff_mem_support_both_of_ZXType
                (vertexStab_is_ZType L xv yv).2 (faceStab_is_XType L xf yf).2 i).1 hi'
            exact ⟨hiZX.2, hiZX.1⟩
          exact (hboth i).1 hi''
        simpa [Finset.mem_insert, Finset.mem_singleton] using hanti.2
      · intro hi
        refine Finset.mem_filter.mpr ?_
        refine ⟨by simp, ?_⟩
        have hi' : i = hh ∨ i = vv := by
          simpa [Finset.mem_insert, Finset.mem_singleton] using hi
        have hanti : C ∧ (i = hh ∨ i = vv) := ⟨hC, hi'⟩
        have hi'' :
            i ∈ (faceStab L xf yf).operators.support ∧
              i ∈ (vertexStab L xv yv).operators.support := (hboth i).2 hanti
        have hiZX :
            i ∈ (vertexStab L xv yv).operators.support ∧
              i ∈ (faceStab L xf yf).operators.support := ⟨hi''.2, hi''.1⟩
        exact (NQubitPauliGroupElement.anticommutesAt_iff_mem_support_both_of_ZXType
          (vertexStab_is_ZType L xv yv).2 (faceStab_is_XType L xf yf).2 i).2 hiZX
    rw [hfilter]
    have hhv : hh ≠ vv := by
      simpa [hh, vv] using (hEdge_ne_vEdge L xf yv xv yf)
    have hnotmem : hh ∉ ({vv} : Finset (Fin (numQubits L))) := by
      simpa [Finset.mem_singleton] using hhv
    rw [Finset.card_insert_of_notMem hnotmem, Finset.card_singleton]
    exact even_two
  · have hfilter :
      (Finset.univ.filter
            (NQubitPauliGroupElement.anticommutesAt
              (vertexStab L xv yv).operators (faceStab L xf yf).operators)) =
        (∅ : Finset (Fin (numQubits L))) := by
      ext i
      constructor
      · intro hi
        exfalso
        have hanti : C ∧ (i = hh ∨ i = vv) := by
          have hi' :
              NQubitPauliGroupElement.anticommutesAt
                (vertexStab L xv yv).operators (faceStab L xf yf).operators i :=
            (Finset.mem_filter.mp hi).2
          have hi'' :
              i ∈ (faceStab L xf yf).operators.support ∧
                i ∈ (vertexStab L xv yv).operators.support := by
            have hiZX :
                i ∈ (vertexStab L xv yv).operators.support ∧
                  i ∈ (faceStab L xf yf).operators.support := by
              exact (NQubitPauliGroupElement.anticommutesAt_iff_mem_support_both_of_ZXType
                (vertexStab_is_ZType L xv yv).2 (faceStab_is_XType L xf yf).2 i).1 hi'
            exact ⟨hiZX.2, hiZX.1⟩
          exact (hboth i).1 hi''
        exact hC hanti.1
      · intro hi
        exact False.elim (Finset.notMem_empty i hi)
    rw [hfilter, Finset.card_empty]
    exact ⟨0, rfl⟩

/-- All toric generators commute pairwise. -/
theorem generators_commute (L : ℕ) [Fact (2 ≤ L)] :
    ∀ g ∈ generators L, ∀ h ∈ generators L, g * h = h * g := by
  intro g hg h hh
  rcases hg with hgZ | hgX <;> rcases hh with hhZ | hhX
  · exact ZGenerators_commute L g hgZ h hhZ
  · exact ZGenerators_commute_XGenerators L g hgZ h hhX
  · rw [NQubitPauliGroupElement.commutes_symm]
    exact ZGenerators_commute_XGenerators L h hhZ g hgX
  · exact XGenerators_commute L g hgX h hhX

/-!
## 5. No `-I` and canonical stabilizer group
-/

/-- Canonical subgroup generated by all toric generators. -/
noncomputable def subgroup (L : ℕ) [Fact (0 < L)] : Subgroup
(NQubitPauliGroupElement (numQubits L)) :=
  Subgroup.closure (generators L)

/-- `-I` is not in the toric stabilizer subgroup. -/
theorem negIdentity_not_mem (L : ℕ) [Fact (2 ≤ L)] :
    StabilizerGroup.negIdentity (numQubits L) ∉ subgroup L := by
  simpa [subgroup, generators] using
    CSSCommutationLemmas.negIdentity_not_mem_closure_union (ZGenerators L) (XGenerators L)
      (ZGenerators_are_ZType L) (XGenerators_are_XType L) (ZGenerators_commute_XGenerators L)

/-- The parametric toric stabilizer group (canonical from generator list). -/
noncomputable def stabilizerGroup (L : ℕ) [Fact (2 ≤ L)] :
    StabilizerGroup (numQubits L) :=
  StabilizerGroup.mkStabilizerFromGenerators (numQubits L) (generatorsList L)
    (by rw [listToSet_generatorsList]; exact generators_commute L)
    (by rw [listToSet_generatorsList]; exact negIdentity_not_mem L)

/-- The bundled stabilizer subgroup equals `subgroup L`. -/
lemma stabilizerGroup_toSubgroup_eq (L : ℕ) [Fact (2 ≤ L)] :
    (stabilizerGroup L).toSubgroup = subgroup L := by
  simp [stabilizerGroup, subgroup, StabilizerGroup.mkStabilizerFromGenerators]
  rw [listToSet_generatorsList]

/-!
## 6. Deferred `StabilizerCode` packaging boundary

Part 1 exposes an explicit constructor boundary so independence/logical-operator packaging
can be proved in a later milestone without refactoring the generator API.
-/

/-- Data required to upgrade `ToricCodeN` to a full `StabilizerCode`. -/
structure CodePackagingData (L : ℕ) [Fact (2 ≤ L)] where
  generators_length : (generatorsList L).length = numQubits L - 2
  generators_phaseZero : NQubitPauliGroupElement.AllPhaseZero (generatorsList L)
  generators_independent : StabilizerGroup.GeneratorsIndependent (numQubits L) (generatorsList L)
  logicalOps : Fin 2 → StabilizerGroup.LogicalQubitOps (numQubits L) (stabilizerGroup L)
  logical_commute_cross : ∀ ℓ ℓ', ℓ ≠ ℓ' →
    ((logicalOps ℓ).xOp * (logicalOps ℓ').xOp = (logicalOps ℓ').xOp * (logicalOps ℓ).xOp ∧
      (logicalOps ℓ).xOp * (logicalOps ℓ').zOp = (logicalOps ℓ').zOp * (logicalOps ℓ).xOp ∧
      (logicalOps ℓ).zOp * (logicalOps ℓ').xOp = (logicalOps ℓ').xOp * (logicalOps ℓ).zOp ∧
      (logicalOps ℓ).zOp * (logicalOps ℓ').zOp = (logicalOps ℓ').zOp * (logicalOps ℓ).zOp)

/-- Build a full `StabilizerCode` from already-established packaging data. -/
noncomputable def stabilizerCodeOfData (L : ℕ) [Fact (2 ≤ L)] (D : CodePackagingData L) :
    StabilizerGroup.StabilizerCode (numQubits L) 2 where
  hk := by
    have hL : 2 ≤ L := Fact.out
    have hq : 2 ≤ numQubits L := by
      dsimp [numQubits]
      nlinarith
    exact hq
  generatorsList := generatorsList L
  generators_length := D.generators_length
  generators_phaseZero := D.generators_phaseZero
  generators_independent := D.generators_independent
  generators_commute := by rw [listToSet_generatorsList]; exact generators_commute L
  closure_no_neg_identity := by rw [listToSet_generatorsList]; exact negIdentity_not_mem L
  logicalOps := D.logicalOps
  logical_commute_cross := D.logical_commute_cross

/-!
## Part 2 aliases (chain complex and homology)
-/

/-- Alias for the toric `∂2` boundary map from the lattice chain-complex layer. -/
abbrev toricBoundary2 (L : ℕ) [Fact (0 < L)] :=
  Stabilizer.Lattice.toricBoundary2 (L := L)

/-- Alias for the toric `∂1` boundary map from the lattice chain-complex layer. -/
abbrev toricBoundary1 (L : ℕ) [Fact (0 < L)] :=
  Stabilizer.Lattice.toricBoundary1 (L := L)

/-- Alias for toric 1-cycles from the lattice homology layer. -/
abbrev toricCycles (L : ℕ) [Fact (0 < L)] :=
  Stabilizer.Lattice.toricCycles (L := L)

/-- Alias for toric 1-boundaries from the lattice homology layer. -/
abbrev toricBoundaries (L : ℕ) [Fact (0 < L)] :=
  Stabilizer.Lattice.toricBoundaries (L := L)

/-- Alias for toric first homology from the lattice homology layer. -/
abbrev toricH1 (L : ℕ) [Fact (0 < L)] :=
  Stabilizer.Lattice.toricH1 (L := L)

/-!
## 7. `L = 2` compatibility checks against `ToricCode8`
-/

/-- `hEdge` indexing at `L=2` matches the concrete qubit numbering used by `ToricCode8`. -/
lemma hEdge_L2_vals :
    ((hEdge 2 0 0).val = 0) ∧ ((hEdge 2 1 0).val = 1) ∧
    ((hEdge 2 0 1).val = 2) ∧ ((hEdge 2 1 1).val = 3) := by decide

/-- `vEdge` indexing at `L=2` matches the concrete qubit numbering used by `ToricCode8`. -/
lemma vEdge_L2_vals :
    ((vEdge 2 0 0).val = 4) ∧ ((vEdge 2 1 0).val = 5) ∧
    ((vEdge 2 0 1).val = 6) ∧ ((vEdge 2 1 1).val = 7) := by decide

/-- At `L=2`, the face stabilizer at `(0,0)` has the same operators as `ToricCode8.B00`. -/
lemma faceStab00_L2_support :
    (faceStab 2 0 0).operators = ToricCode8.B00.operators := by
  ext i
  fin_cases i <;> decide

/-- At `L=2`, the vertex stabilizer at `(0,0)` has the same operators as `ToricCode8.A00`. -/
lemma vertexStab00_L2_support :
    (vertexStab 2 0 0).operators = ToricCode8.A00.operators := by
  ext i
  fin_cases i <;> decide

end ToricCodeN
end StabilizerGroup
end Quantum
