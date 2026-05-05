import QEC.Stabilizer.Codes.ToricCodeN
import QEC.Stabilizer.Codes.ToricCodeNDistanceX
import QEC.Stabilizer.Codes.ToricCodeNDistanceZ
import QEC.Stabilizer.Core.StabilizerCode
import QEC.Stabilizer.Core.LogicalOperators
import QEC.Stabilizer.Lattice.ToricH1Dimension
import QEC.Stabilizer.Lattice.ToricLogicalCorrespondenceX
import QEC.Stabilizer.Lattice.ToricLogicalCorrespondenceZ

/-!
# Toric code as `StabilizerCode (2L², 2)`

Upgrades the toric stabilizer family to a full `StabilizerCode (numQubits L) 2`,
encoding 2 logical qubits.

Status: **All sub-lemmas proven.**
  * `dropped_vertex_in_closure_remaining`, `dropped_face_in_closure_remaining` —
    the homological identities.
  * `closure_packaged_eq_full` — closure equality.
  * `toric_logicalOps`, `toric_logical_commute_cross` — the four logical loop
    operators and their commutation matrix.
  * `generators_independent_packaged` — symplectic linear independence of the
    `2L² - 2` trimmed rows (the toric rank theorem). Proven via block-anti-diagonal
    structure of the check matrix and the kernel characterizations
    `mem_ker_cutMap_iff` / `mem_ker_boundary2_iff`.
-/

namespace Quantum
namespace StabilizerGroup
namespace ToricCodeN

open NQubitPauliGroupElement
open Stabilizer.Lattice

-- ---------------------------------------------------------------------------
-- Phase 1.1: Trimmed coordinate and generator lists
-- ---------------------------------------------------------------------------

/-- Distinguished "origin" coordinate `(0, 0)` — the vertex/face we drop. -/
private def originCoord (L : ℕ) [Fact (0 < L)] : Fin L × Fin L :=
  (zeroCoord L, zeroCoord L)

/-- Coordinates with the origin removed; has `L² - 1` entries. -/
def coordsTrimmed (L : ℕ) [Fact (0 < L)] : List (Fin L × Fin L) :=
  (coords L).filter (fun p => decide (p ≠ originCoord L))

/-- Trimmed Z-generator list: vertex stabs over all but the origin. -/
def generatorsListZTrimmed (L : ℕ) [Fact (0 < L)] :
    List (NQubitPauliGroupElement (numQubits L)) :=
  (coordsTrimmed L).map (fun p => vertexStab L p.1 p.2)

/-- Trimmed X-generator list: face stabs over all but the origin. -/
def generatorsListXTrimmed (L : ℕ) [Fact (0 < L)] :
    List (NQubitPauliGroupElement (numQubits L)) :=
  (coordsTrimmed L).map (fun p => faceStab L p.1 p.2)

/-- Packaged generator list: trimmed Z-generators followed by trimmed X-generators.
Length is `2L² - 2 = numQubits L - 2`. -/
def generatorsListPackaged (L : ℕ) [Fact (0 < L)] :
    List (NQubitPauliGroupElement (numQubits L)) :=
  generatorsListZTrimmed L ++ generatorsListXTrimmed L

-- ---------------------------------------------------------------------------
-- Phase 1.2: Length, phase-zero, pairwise-commute helpers
-- ---------------------------------------------------------------------------

/-- The (untrimmed) coords list has length `L²`. -/
private lemma coords_length (L : ℕ) : (coords L).length = L * L := by
  show ((List.finRange L).product (List.finRange L)).length = L * L
  unfold List.product
  simp [List.length_flatMap]

/-- The trimmed coords list has length `L² - 1`. -/
private lemma coordsTrimmed_length (L : ℕ) [Fact (0 < L)] :
    (coordsTrimmed L).length = L * L - 1 := by
  classical
  have hL : 0 < L := Fact.out
  have hnodup : (coords L).Nodup := by
    show ((List.finRange L).product (List.finRange L)).Nodup
    exact List.Nodup.product (List.nodup_finRange L) (List.nodup_finRange L)
  have horigin_mem : originCoord L ∈ coords L := by
    show originCoord L ∈ (List.finRange L).product (List.finRange L)
    rcases h : originCoord L with ⟨x, y⟩
    simp
  have hnodup_trim : (coordsTrimmed L).Nodup := hnodup.filter _
  have h_trim_set :
      (coordsTrimmed L).toFinset =
        (Finset.univ : Finset (Fin L × Fin L)).erase (originCoord L) := by
    ext p
    simp only [List.mem_toFinset, coordsTrimmed, List.mem_filter, Finset.mem_erase,
      Finset.mem_univ, decide_eq_true_eq, and_true]
    constructor
    · rintro ⟨_, hne⟩; exact hne
    · intro hne
      refine ⟨?_, hne⟩
      rcases p with ⟨x, y⟩
      show (x, y) ∈ (List.finRange L).product (List.finRange L)
      simp
  rw [← List.toFinset_card_of_nodup hnodup_trim, h_trim_set,
      Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin]

/-- The packaged list has length `numQubits L - 2 = 2L² - 2`. -/
lemma generatorsListPackaged_length (L : ℕ) [Fact (0 < L)] :
    (generatorsListPackaged L).length = numQubits L - 2 := by
  unfold generatorsListPackaged generatorsListZTrimmed generatorsListXTrimmed numQubits
  rw [List.length_append, List.length_map, List.length_map, coordsTrimmed_length]
  have hL : 0 < L := Fact.out
  have h1 : 1 ≤ L * L := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h2L : 2 * L * L = 2 * (L * L) := by ring
  omega

/-- All elements of the trimmed Z-list have phase 0. -/
private lemma allPhaseZero_genListZTrimmed (L : ℕ) [Fact (0 < L)] :
    AllPhaseZero (generatorsListZTrimmed L) := by
  intro g hg
  rcases List.mem_map.mp hg with ⟨p, _, rfl⟩
  rfl

/-- All elements of the trimmed X-list have phase 0. -/
private lemma allPhaseZero_genListXTrimmed (L : ℕ) [Fact (0 < L)] :
    AllPhaseZero (generatorsListXTrimmed L) := by
  intro g hg
  rcases List.mem_map.mp hg with ⟨p, _, rfl⟩
  rfl

/-- All elements of the packaged generator list have phase 0. -/
lemma allPhaseZero_generatorsListPackaged (L : ℕ) [Fact (0 < L)] :
    AllPhaseZero (generatorsListPackaged L) := by
  intro g hg
  rcases List.mem_append.mp hg with hZ | hX
  · exact allPhaseZero_genListZTrimmed L g hZ
  · exact allPhaseZero_genListXTrimmed L g hX

/-- The trimmed Z-list is a subset of the original Z-generator set. -/
private lemma listToSet_genListZTrimmed_subset (L : ℕ) [Fact (0 < L)] :
    listToSet (generatorsListZTrimmed L) ⊆ ZGenerators L := by
  intro g hg
  rcases List.mem_map.mp hg with ⟨p, _, rfl⟩
  exact ⟨p, rfl⟩

/-- The trimmed X-list is a subset of the original X-generator set. -/
private lemma listToSet_genListXTrimmed_subset (L : ℕ) [Fact (0 < L)] :
    listToSet (generatorsListXTrimmed L) ⊆ XGenerators L := by
  intro g hg
  rcases List.mem_map.mp hg with ⟨p, _, rfl⟩
  exact ⟨p, rfl⟩

/-- The packaged list is a subset of the union of the original Z- and X-generator sets. -/
lemma listToSet_packaged_subset_full (L : ℕ) [Fact (0 < L)] :
    listToSet (generatorsListPackaged L) ⊆ generators L := by
  intro g hg
  rcases List.mem_append.mp hg with hZ | hX
  · exact Or.inl (listToSet_genListZTrimmed_subset L hZ)
  · exact Or.inr (listToSet_genListXTrimmed_subset L hX)

/-- The packaged generators pairwise commute (subset of full generators which commute). -/
lemma generators_commute_packaged (L : ℕ) [Fact (2 ≤ L)] :
    ∀ g ∈ listToSet (generatorsListPackaged L),
    ∀ h ∈ listToSet (generatorsListPackaged L), g * h = h * g := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  intro g hg h hh
  exact generators_commute L g (listToSet_packaged_subset_full L hg)
    h (listToSet_packaged_subset_full L hh)

-- ---------------------------------------------------------------------------
-- Phase 1.3 / 1.4: Homological identities
-- ---------------------------------------------------------------------------

/-- The cut map sends the constant-1 0-chain to the zero 1-chain (each edge
collects `1 + 1 = 0` from its two incident vertices). -/
private lemma toricVertexCutMap_constOne (L : ℕ) [Fact (0 < L)] :
    Stabilizer.Lattice.toricVertexCutMap (L := L) (fun _ : Fin L × Fin L => (1 : ZMod 2)) = 0 := by
  ext e
  have h : (1 : ZMod 2) + 1 = 0 := by decide
  cases e <;> simp [Stabilizer.Lattice.toricVertexCutMap, h]

/-- `∂₂` sends the constant-1 2-chain to zero (each edge collects `1 + 1 = 0`). -/
private lemma toricBoundary2_constOne (L : ℕ) [Fact (0 < L)] :
    Stabilizer.Lattice.toricBoundary2 (L := L) (fun _ : Fin L × Fin L => (1 : ZMod 2)) = 0 := by
  ext e
  have h : (1 : ZMod 2) + 1 = 0 := by decide
  cases e <;> simp [Stabilizer.Lattice.toricBoundary2, h]

/-- The list product of vertex stabs over a list of coordinates equals the
Z-operator-of-chain applied to the cutMap of the corresponding sum of single-vtx
indicators. -/
private lemma vertexStab_listProd_eq_chain (L : ℕ) [Fact (2 ≤ L)]
    (lst : List (Fin L × Fin L)) :
    (lst.map (fun p => vertexStab L p.1 p.2)).prod =
      Stabilizer.Lattice.toricZOperatorOfChain L
        (Stabilizer.Lattice.toricVertexCutMap (L := L)
          ((lst.map (fun p => Stabilizer.Lattice.singleVtx (L := L) p)).sum)) := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  induction lst with
  | nil =>
      simp only [List.map_nil, List.prod_nil, List.sum_nil]
      rw [LinearMap.map_zero, Stabilizer.Lattice.toricZOperatorOfChain_zero]
  | cons p tail ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [LinearMap.map_add, Stabilizer.Lattice.toricZOperatorOfChain_add,
        Stabilizer.Lattice.toricZOperatorOfChain_cutMap_singleVtx, ih]

/-- Symmetric version for X-side: list product of face stabs = X-operator of `∂₂` of
sum of single-face indicators. -/
private lemma faceStab_listProd_eq_chain (L : ℕ) [Fact (2 ≤ L)]
    (lst : List (Fin L × Fin L)) :
    (lst.map (fun p => faceStab L p.1 p.2)).prod =
      Stabilizer.Lattice.toricXOperatorOfChain L
        (Stabilizer.Lattice.toricBoundary2 (L := L)
          ((lst.map (fun p => Stabilizer.Lattice.singleFace (L := L) p)).sum)) := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  induction lst with
  | nil =>
      simp only [List.map_nil, List.prod_nil, List.sum_nil]
      rw [LinearMap.map_zero, Stabilizer.Lattice.toricXOperatorOfChain_zero]
  | cons p tail ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [LinearMap.map_add, Stabilizer.Lattice.toricXOperatorOfChain_add,
        Stabilizer.Lattice.toricXOperatorOfChain_boundary_singleFace, ih]

/-- The sum (as 0-chains) of `singleVtx p` over all `p ∈ coords L` is the
constant-1 chain. -/
private lemma sum_singleVtx_coords (L : ℕ) [Fact (0 < L)] :
    ((coords L).map (fun p => Stabilizer.Lattice.singleVtx (L := L) p)).sum =
      (fun _ => (1 : ZMod 2)) := by
  have h_nodup : (coords L).Nodup := by
    show ((List.finRange L).product (List.finRange L)).Nodup
    exact List.Nodup.product (List.nodup_finRange L) (List.nodup_finRange L)
  have h_finset_eq : (coords L).toFinset = (Finset.univ : Finset (Fin L × Fin L)) := by
    ext p
    refine ⟨fun _ => Finset.mem_univ _, fun _ => List.mem_toFinset.mpr (mem_coords L p)⟩
  rw [show ((coords L).map (fun p => Stabilizer.Lattice.singleVtx (L := L) p)).sum =
      ∑ p ∈ Finset.univ, Stabilizer.Lattice.singleVtx (L := L) p from ?_]
  · ext v
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single v]
    · simp [Stabilizer.Lattice.singleVtx]
    · intro b _ hbne
      have : Stabilizer.Lattice.singleVtx (L := L) b v = 0 :=
        Stabilizer.Lattice.singleVtx_apply_ne hbne.symm
      exact this
    · intro hcontra; exact absurd (Finset.mem_univ v) hcontra
  · rw [show (Finset.univ : Finset (Fin L × Fin L)) = (coords L).toFinset from h_finset_eq.symm]
    exact (List.sum_toFinset _ h_nodup).symm

/-- Symmetric: sum of `singleFace p` over `coords L` is the constant-1 2-chain. -/
private lemma sum_singleFace_coords (L : ℕ) [Fact (0 < L)] :
    ((coords L).map (fun p => Stabilizer.Lattice.singleFace (L := L) p)).sum =
      (fun _ => (1 : ZMod 2)) := by
  have h_nodup : (coords L).Nodup := by
    show ((List.finRange L).product (List.finRange L)).Nodup
    exact List.Nodup.product (List.nodup_finRange L) (List.nodup_finRange L)
  have h_finset_eq : (coords L).toFinset = (Finset.univ : Finset (Fin L × Fin L)) := by
    ext p
    refine ⟨fun _ => Finset.mem_univ _, fun _ => List.mem_toFinset.mpr (mem_coords L p)⟩
  rw [show ((coords L).map (fun p => Stabilizer.Lattice.singleFace (L := L) p)).sum =
      ∑ p ∈ Finset.univ, Stabilizer.Lattice.singleFace (L := L) p from ?_]
  · ext v
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single v]
    · simp [Stabilizer.Lattice.singleFace]
    · intro b _ hbne
      exact Stabilizer.Lattice.singleFace_apply_ne hbne.symm
    · intro hcontra; exact absurd (Finset.mem_univ v) hcontra
  · rw [show (Finset.univ : Finset (Fin L × Fin L)) = (coords L).toFinset from h_finset_eq.symm]
    exact (List.sum_toFinset _ h_nodup).symm

/-- Decompose `coords L` sum as `coordsTrimmed L` sum plus origin. -/
private lemma sum_singleVtx_coords_eq_trimmed_add_origin (L : ℕ) [Fact (0 < L)] :
    ((coords L).map (fun p => Stabilizer.Lattice.singleVtx (L := L) p)).sum =
      ((coordsTrimmed L).map (fun p => Stabilizer.Lattice.singleVtx (L := L) p)).sum
        + Stabilizer.Lattice.singleVtx (L := L) (originCoord L) := by
  have h_nodup : (coords L).Nodup := by
    show ((List.finRange L).product (List.finRange L)).Nodup
    exact List.Nodup.product (List.nodup_finRange L) (List.nodup_finRange L)
  have h_finset_eq : (coords L).toFinset = (Finset.univ : Finset (Fin L × Fin L)) := by
    ext p
    refine ⟨fun _ => Finset.mem_univ _, fun _ => List.mem_toFinset.mpr (mem_coords L p)⟩
  classical
  have h_nodup_trim : (coordsTrimmed L).Nodup := h_nodup.filter _
  have h_trim_finset : (coordsTrimmed L).toFinset =
      (Finset.univ : Finset (Fin L × Fin L)).erase (originCoord L) := by
    ext p
    simp only [List.mem_toFinset, coordsTrimmed, List.mem_filter, Finset.mem_erase,
      Finset.mem_univ, decide_eq_true_eq, and_true]
    refine ⟨fun ⟨_, h⟩ => h, fun h => ⟨List.mem_toFinset.mp ((show
      (coords L).toFinset = (Finset.univ : Finset (Fin L × Fin L)) from h_finset_eq) ▸
      Finset.mem_univ p), h⟩⟩
  -- Convert both sides to Finset.sum and apply Finset.sum_erase_eq_sub-style.
  rw [show ((coords L).map (fun p => Stabilizer.Lattice.singleVtx (L := L) p)).sum =
      ∑ p ∈ Finset.univ, Stabilizer.Lattice.singleVtx (L := L) p from ?_,
      show ((coordsTrimmed L).map (fun p => Stabilizer.Lattice.singleVtx (L := L) p)).sum =
      ∑ p ∈ (Finset.univ : Finset (Fin L × Fin L)).erase (originCoord L),
        Stabilizer.Lattice.singleVtx (L := L) p from ?_]
  · rw [Finset.sum_erase_add _ _ (Finset.mem_univ (originCoord L))]
  · rw [show ((Finset.univ : Finset (Fin L × Fin L)).erase (originCoord L)) =
        (coordsTrimmed L).toFinset from h_trim_finset.symm]
    exact (List.sum_toFinset _ h_nodup_trim).symm
  · rw [show (Finset.univ : Finset (Fin L × Fin L)) = (coords L).toFinset from h_finset_eq.symm]
    exact (List.sum_toFinset _ h_nodup).symm

/-- Symmetric: decompose `coords L` face sum. -/
private lemma sum_singleFace_coords_eq_trimmed_add_origin (L : ℕ) [Fact (0 < L)] :
    ((coords L).map (fun p => Stabilizer.Lattice.singleFace (L := L) p)).sum =
      ((coordsTrimmed L).map (fun p => Stabilizer.Lattice.singleFace (L := L) p)).sum
        + Stabilizer.Lattice.singleFace (L := L) (originCoord L) := by
  have h_nodup : (coords L).Nodup := by
    show ((List.finRange L).product (List.finRange L)).Nodup
    exact List.Nodup.product (List.nodup_finRange L) (List.nodup_finRange L)
  have h_finset_eq : (coords L).toFinset = (Finset.univ : Finset (Fin L × Fin L)) := by
    ext p
    refine ⟨fun _ => Finset.mem_univ _, fun _ => List.mem_toFinset.mpr (mem_coords L p)⟩
  classical
  have h_nodup_trim : (coordsTrimmed L).Nodup := h_nodup.filter _
  have h_trim_finset : (coordsTrimmed L).toFinset =
      (Finset.univ : Finset (Fin L × Fin L)).erase (originCoord L) := by
    ext p
    simp only [List.mem_toFinset, coordsTrimmed, List.mem_filter, Finset.mem_erase,
      Finset.mem_univ, decide_eq_true_eq, and_true]
    refine ⟨fun ⟨_, h⟩ => h, fun h => ⟨List.mem_toFinset.mp ((show
      (coords L).toFinset = (Finset.univ : Finset (Fin L × Fin L)) from h_finset_eq) ▸
      Finset.mem_univ p), h⟩⟩
  rw [show ((coords L).map (fun p => Stabilizer.Lattice.singleFace (L := L) p)).sum =
      ∑ p ∈ Finset.univ, Stabilizer.Lattice.singleFace (L := L) p from ?_,
      show ((coordsTrimmed L).map (fun p => Stabilizer.Lattice.singleFace (L := L) p)).sum =
      ∑ p ∈ (Finset.univ : Finset (Fin L × Fin L)).erase (originCoord L),
        Stabilizer.Lattice.singleFace (L := L) p from ?_]
  · rw [Finset.sum_erase_add _ _ (Finset.mem_univ (originCoord L))]
  · rw [show ((Finset.univ : Finset (Fin L × Fin L)).erase (originCoord L)) =
        (coordsTrimmed L).toFinset from h_trim_finset.symm]
    exact (List.sum_toFinset _ h_nodup_trim).symm
  · rw [show (Finset.univ : Finset (Fin L × Fin L)) = (coords L).toFinset from h_finset_eq.symm]
    exact (List.sum_toFinset _ h_nodup).symm

/-- Homological identity: dropped vertex stab is in the closure of the remaining
vertex stabs. Equivalent to `∏ all vertex stabs = I`. -/
private theorem dropped_vertex_in_closure_remaining (L : ℕ) [Fact (2 ≤ L)] :
    vertexStab L (zeroCoord L) (zeroCoord L) ∈
      Subgroup.closure (listToSet (generatorsListZTrimmed L)) := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  -- Step 1: cutMap (trimmed sum) = cutMap (singleVtx origin).
  have h_decomp := sum_singleVtx_coords_eq_trimmed_add_origin L
  have h_const := sum_singleVtx_coords L
  have h_trim_plus_origin :
      ((coordsTrimmed L).map (fun p => Stabilizer.Lattice.singleVtx (L := L) p)).sum
        + Stabilizer.Lattice.singleVtx (L := L) (originCoord L) =
      (fun _ : Fin L × Fin L => (1 : ZMod 2)) := h_decomp ▸ h_const
  have h_cutMap_trim_eq :
      Stabilizer.Lattice.toricVertexCutMap (L := L)
          (((coordsTrimmed L).map (fun p => Stabilizer.Lattice.singleVtx (L := L) p)).sum)
        = Stabilizer.Lattice.toricVertexCutMap (L := L)
            (Stabilizer.Lattice.singleVtx (L := L) (originCoord L)) := by
    have h_apply := congrArg (Stabilizer.Lattice.toricVertexCutMap (L := L)) h_trim_plus_origin
    rw [LinearMap.map_add, toricVertexCutMap_constOne] at h_apply
    -- h_apply : cutMap trim + cutMap (singleVtx origin) = 0.
    -- In ZMod 2, a + b = 0 implies a = b.
    have h_self_zero : ∀ a : ZMod 2, a + a = 0 := fun a => by
      have h2 : (2 : ZMod 2) = 0 := by decide
      calc a + a = (2 : ZMod 2) * a := by ring
        _ = 0 := by rw [h2, zero_mul]
    ext e
    have he : (Stabilizer.Lattice.toricVertexCutMap (L := L)
        (((coordsTrimmed L).map (fun p => Stabilizer.Lattice.singleVtx (L := L) p)).sum)) e +
        (Stabilizer.Lattice.toricVertexCutMap (L := L)
        (Stabilizer.Lattice.singleVtx (L := L) (originCoord L))) e = 0 :=
      congrFun h_apply e
    have heq : (Stabilizer.Lattice.toricVertexCutMap (L := L)
        (((coordsTrimmed L).map (fun p => Stabilizer.Lattice.singleVtx (L := L) p)).sum)) e =
        (Stabilizer.Lattice.toricVertexCutMap (L := L)
        (Stabilizer.Lattice.singleVtx (L := L) (originCoord L))) e := by
      have hself := h_self_zero (Stabilizer.Lattice.toricVertexCutMap (L := L)
        (Stabilizer.Lattice.singleVtx (L := L) (originCoord L)) e)
      -- From he and hself, conclude
      have : (Stabilizer.Lattice.toricVertexCutMap (L := L)
        (((coordsTrimmed L).map (fun p => Stabilizer.Lattice.singleVtx (L := L) p)).sum)) e +
        (Stabilizer.Lattice.toricVertexCutMap (L := L)
        (Stabilizer.Lattice.singleVtx (L := L) (originCoord L))) e =
        (Stabilizer.Lattice.toricVertexCutMap (L := L)
        (Stabilizer.Lattice.singleVtx (L := L) (originCoord L))) e +
        (Stabilizer.Lattice.toricVertexCutMap (L := L)
        (Stabilizer.Lattice.singleVtx (L := L) (originCoord L))) e := by
        rw [he, hself]
      exact add_right_cancel this
    exact heq
  -- Step 2: vertexStab origin = list-prod (trimmed)
  have h_prod_eq : (generatorsListZTrimmed L).prod = vertexStab L (zeroCoord L) (zeroCoord L) := by
    unfold generatorsListZTrimmed
    rw [vertexStab_listProd_eq_chain L (coordsTrimmed L), h_cutMap_trim_eq,
      Stabilizer.Lattice.toricZOperatorOfChain_cutMap_singleVtx]
    rfl
  -- Step 3: list-prod of trimmed is in closure
  have h_prod_in_closure : (generatorsListZTrimmed L).prod ∈
      Subgroup.closure (listToSet (generatorsListZTrimmed L)) := by
    apply list_prod_mem
    intro g hg
    rcases List.mem_iff_get.mp hg with ⟨i, hi⟩
    -- g ∈ generatorsListZTrimmed L, so g ∈ listToSet (generatorsListZTrimmed L)
    have h_mem_list : g ∈ generatorsListZTrimmed L := List.mem_iff_get.mpr ⟨i, hi⟩
    exact Subgroup.subset_closure h_mem_list
  -- Conclude
  exact h_prod_eq ▸ h_prod_in_closure

/-- Homological identity: dropped face stab is in the closure of the remaining face
stabs. Equivalent to `∏ all face stabs = I`. Symmetric proof to the vertex case via
`toricXOperatorOfChain_boundary_singleFace` and `toricBoundary2`. -/
private theorem dropped_face_in_closure_remaining (L : ℕ) [Fact (2 ≤ L)] :
    faceStab L (zeroCoord L) (zeroCoord L) ∈
      Subgroup.closure (listToSet (generatorsListXTrimmed L)) := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  have h_decomp := sum_singleFace_coords_eq_trimmed_add_origin L
  have h_const := sum_singleFace_coords L
  have h_trim_plus_origin :
      ((coordsTrimmed L).map (fun p => Stabilizer.Lattice.singleFace (L := L) p)).sum
        + Stabilizer.Lattice.singleFace (L := L) (originCoord L) =
      (fun _ : Fin L × Fin L => (1 : ZMod 2)) := h_decomp ▸ h_const
  have h_b2_trim_eq :
      Stabilizer.Lattice.toricBoundary2 (L := L)
          (((coordsTrimmed L).map (fun p => Stabilizer.Lattice.singleFace (L := L) p)).sum)
        = Stabilizer.Lattice.toricBoundary2 (L := L)
            (Stabilizer.Lattice.singleFace (L := L) (originCoord L)) := by
    have h_apply := congrArg (Stabilizer.Lattice.toricBoundary2 (L := L)) h_trim_plus_origin
    rw [LinearMap.map_add, toricBoundary2_constOne] at h_apply
    have h_self_zero : ∀ a : ZMod 2, a + a = 0 := fun a => by
      have h2 : (2 : ZMod 2) = 0 := by decide
      calc a + a = (2 : ZMod 2) * a := by ring
        _ = 0 := by rw [h2, zero_mul]
    ext e
    have he : (Stabilizer.Lattice.toricBoundary2 (L := L)
        (((coordsTrimmed L).map (fun p => Stabilizer.Lattice.singleFace (L := L) p)).sum)) e +
        (Stabilizer.Lattice.toricBoundary2 (L := L)
        (Stabilizer.Lattice.singleFace (L := L) (originCoord L))) e = 0 :=
      congrFun h_apply e
    have hself := h_self_zero (Stabilizer.Lattice.toricBoundary2 (L := L)
      (Stabilizer.Lattice.singleFace (L := L) (originCoord L)) e)
    have : (Stabilizer.Lattice.toricBoundary2 (L := L)
      (((coordsTrimmed L).map (fun p => Stabilizer.Lattice.singleFace (L := L) p)).sum)) e +
      (Stabilizer.Lattice.toricBoundary2 (L := L)
      (Stabilizer.Lattice.singleFace (L := L) (originCoord L))) e =
      (Stabilizer.Lattice.toricBoundary2 (L := L)
      (Stabilizer.Lattice.singleFace (L := L) (originCoord L))) e +
      (Stabilizer.Lattice.toricBoundary2 (L := L)
      (Stabilizer.Lattice.singleFace (L := L) (originCoord L))) e := by
      rw [he, hself]
    exact add_right_cancel this
  have h_prod_eq : (generatorsListXTrimmed L).prod = faceStab L (zeroCoord L) (zeroCoord L) := by
    unfold generatorsListXTrimmed
    rw [faceStab_listProd_eq_chain L (coordsTrimmed L), h_b2_trim_eq,
      Stabilizer.Lattice.toricXOperatorOfChain_boundary_singleFace]
    rfl
  have h_prod_in_closure : (generatorsListXTrimmed L).prod ∈
      Subgroup.closure (listToSet (generatorsListXTrimmed L)) := by
    apply list_prod_mem
    intro g hg
    rcases List.mem_iff_get.mp hg with ⟨i, hi⟩
    have h_mem_list : g ∈ generatorsListXTrimmed L := List.mem_iff_get.mpr ⟨i, hi⟩
    exact Subgroup.subset_closure h_mem_list
  exact h_prod_eq ▸ h_prod_in_closure

-- ---------------------------------------------------------------------------
-- Phase 1.5: Closure equality
-- ---------------------------------------------------------------------------

/-- The closure of the packaged trimmed list equals the closure of the full
generator set, hence equals `(stabilizerGroup L).toSubgroup`. Uses the homological
identities (dropped generator ∈ closure of remaining). -/
lemma closure_packaged_eq_full (L : ℕ) [Fact (2 ≤ L)] :
    Subgroup.closure (listToSet (generatorsListPackaged L)) =
      (stabilizerGroup L).toSubgroup := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  rw [stabilizerGroup_toSubgroup_eq, subgroup]
  apply le_antisymm
  · -- ⊆: closure(trimmed) ⊆ closure(full) since trimmed ⊆ full
    exact Subgroup.closure_mono (listToSet_packaged_subset_full L)
  · -- ⊇: every full generator is in closure(trimmed)
    apply Subgroup.closure_le _ |>.mpr
    -- The trimmed Z-list is a subset of the packaged list
    have hZ_in_packaged :
        listToSet (generatorsListZTrimmed L) ⊆ listToSet (generatorsListPackaged L) := by
      intro g hg
      exact List.mem_append_left _ hg
    have hX_in_packaged :
        listToSet (generatorsListXTrimmed L) ⊆ listToSet (generatorsListPackaged L) := by
      intro g hg
      exact List.mem_append_right _ hg
    rintro g (hZ | hX)
    · -- g is a vertex stab vertexStab L x y
      rcases hZ with ⟨⟨x, y⟩, rfl⟩
      by_cases h_orig : (x, y) = originCoord L
      · -- the dropped vertex
        obtain ⟨hx, hy⟩ := Prod.mk_inj.mp h_orig
        subst hx; subst hy
        exact (Subgroup.closure_mono hZ_in_packaged) (dropped_vertex_in_closure_remaining L)
      · -- non-dropped vertex stab is in trimmed Z
        apply Subgroup.subset_closure
        apply hZ_in_packaged
        refine List.mem_map.mpr ⟨(x, y), ?_, rfl⟩
        unfold coordsTrimmed
        refine List.mem_filter.mpr ⟨?_, by simpa using h_orig⟩
        show (x, y) ∈ (List.finRange L).product (List.finRange L)
        simp
    · -- g is a face stab faceStab L x y
      rcases hX with ⟨⟨x, y⟩, rfl⟩
      by_cases h_orig : (x, y) = originCoord L
      · obtain ⟨hx, hy⟩ := Prod.mk_inj.mp h_orig
        subst hx; subst hy
        exact (Subgroup.closure_mono hX_in_packaged) (dropped_face_in_closure_remaining L)
      · apply Subgroup.subset_closure
        apply hX_in_packaged
        refine List.mem_map.mpr ⟨(x, y), ?_, rfl⟩
        unfold coordsTrimmed
        refine List.mem_filter.mpr ⟨?_, by simpa using h_orig⟩
        show (x, y) ∈ (List.finRange L).product (List.finRange L)
        simp

/-- `-I` is not in the closure of the packaged generator list. -/
lemma negIdentity_not_mem_packaged (L : ℕ) [Fact (2 ≤ L)] :
    StabilizerGroup.negIdentity (numQubits L) ∉
      Subgroup.closure (listToSet (generatorsListPackaged L)) := by
  rw [closure_packaged_eq_full L, stabilizerGroup_toSubgroup_eq]
  exact negIdentity_not_mem L

-- ---------------------------------------------------------------------------
-- Phase 2: Logical loop operators
-- ---------------------------------------------------------------------------

/-- Vertical X-loop chain: V-edges along column `x = zeroCoord`. -/
def verticalLoopChain (L : ℕ) [Fact (0 < L)] : Stabilizer.Lattice.C1 L :=
  fun e =>
    match e with
    | Stabilizer.Lattice.EdgeIdx.h _ _ => 0
    | Stabilizer.Lattice.EdgeIdx.v x _ =>
        if x = Stabilizer.Lattice.zeroCoord L then (1 : ZMod 2) else 0

/-- X-type Pauli operator encoded by the vertical loop chain. -/
def verticalLoopXOperator (L : ℕ) [Fact (0 < L)] :
    NQubitPauliGroupElement (Stabilizer.Lattice.toricNumQubits L) :=
  Stabilizer.Lattice.toricXOperatorOfChain L (verticalLoopChain L)

/-- Horizontal Z-row chain: H-edges along column `x = zeroCoord`. -/
def horizontalHRowChain (L : ℕ) [Fact (0 < L)] : Stabilizer.Lattice.C1 L :=
  fun e =>
    match e with
    | Stabilizer.Lattice.EdgeIdx.h x _ =>
        if x = Stabilizer.Lattice.zeroCoord L then (1 : ZMod 2) else 0
    | Stabilizer.Lattice.EdgeIdx.v _ _ => 0

/-- Z-type Pauli operator encoded by the horizontal H-row chain. -/
def horizontalHRowZOperator (L : ℕ) [Fact (0 < L)] :
    NQubitPauliGroupElement (Stabilizer.Lattice.toricNumQubits L) :=
  Stabilizer.Lattice.toricZOperatorOfChain L (horizontalHRowChain L)

/-- The vertical X-loop chain is a primal cycle. -/
theorem verticalLoopChain_mem_toricCycles (L : ℕ) [Fact (2 ≤ L)] :
    verticalLoopChain L ∈ Stabilizer.Lattice.toricCycles (L := L) := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  unfold Stabilizer.Lattice.toricCycles
  rw [LinearMap.mem_ker]
  ext ⟨xv, yv⟩
  simp only [Stabilizer.Lattice.toricBoundary1, LinearMap.coe_mk, AddHom.coe_mk,
    verticalLoopChain]
  by_cases hx : xv = Stabilizer.Lattice.zeroCoord L
  · subst hx
    show (0 : ZMod 2) + 0 + 1 + 1 = 0
    decide
  · simp [hx]

/-- The vertical X-loop chain is not a primal boundary (its `vAt` invariant is 1). -/
theorem verticalLoopChain_not_mem_toricBoundaries (L : ℕ) [Fact (2 ≤ L)] :
    verticalLoopChain L ∉ Stabilizer.Lattice.toricBoundaries (L := L) := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  intro h
  have h_vAt : Stabilizer.Lattice.vAt (L := L) (Stabilizer.Lattice.zeroCoord L)
      (verticalLoopChain L) = 0 :=
    Stabilizer.Lattice.v_boundary_zero (L := L) ⟨verticalLoopChain L, h⟩
  have h_compute : Stabilizer.Lattice.vAt (L := L) (Stabilizer.Lattice.zeroCoord L)
      (verticalLoopChain L) = 1 := by
    unfold Stabilizer.Lattice.vAt verticalLoopChain
    rw [Finset.sum_eq_single (Stabilizer.Lattice.zeroCoord L)]
    · simp
    · intro b _ hbne
      simp [hbne]
    · intro hcontra; exact absurd (Finset.mem_univ _) hcontra
  rw [h_compute] at h_vAt
  exact absurd h_vAt (by decide)

/-- The vertical X-loop chain has edge weight `L`. -/
theorem verticalLoopChain_edgeWeight_eq_L (L : ℕ) [Fact (2 ≤ L)] :
    Stabilizer.Lattice.edgeWeight (L := L) (verticalLoopChain L) = L := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  let z0 : Fin L := Stabilizer.Lattice.zeroCoord L
  let vertCol : Finset (Stabilizer.Lattice.EdgeIdx L) :=
    (Finset.univ.image (fun y : Fin L => Stabilizer.Lattice.EdgeIdx.v z0 y))
  have hsupport :
      Stabilizer.Lattice.edgeSupport (L := L) (verticalLoopChain L) = vertCol := by
    ext e
    constructor
    · intro he
      have hne : verticalLoopChain L e ≠ 0 := by
        simpa [Stabilizer.Lattice.mem_edgeSupport] using he
      cases e with
      | h x y => simp [verticalLoopChain] at hne
      | v x y =>
          by_cases hx : x = z0
          · subst hx
            refine Finset.mem_image.mpr ?_
            exact ⟨y, Finset.mem_univ y, rfl⟩
          · have hx' : x = z0 := by simpa [verticalLoopChain] using hne
            exact (hx hx').elim
    · intro he
      rcases Finset.mem_image.mp he with ⟨y, -, hy⟩
      subst hy
      simp [Stabilizer.Lattice.mem_edgeSupport, verticalLoopChain, z0]
  have hinj : Function.Injective (fun y : Fin L => Stabilizer.Lattice.EdgeIdx.v z0 y) := by
    intro a b h; cases h; rfl
  have hcard : vertCol.card = L := by
    calc
      vertCol.card
          = (Finset.univ.image (fun y : Fin L => Stabilizer.Lattice.EdgeIdx.v z0 y)).card := rfl
      _ = (Finset.univ : Finset (Fin L)).card := by
          exact Finset.card_image_of_injective
            (s := (Finset.univ : Finset (Fin L)))
            (f := fun y : Fin L => Stabilizer.Lattice.EdgeIdx.v z0 y)
            (by intro a b hab; exact hinj hab)
      _ = L := by simp
  calc
    Stabilizer.Lattice.edgeWeight (L := L) (verticalLoopChain L)
        = (Stabilizer.Lattice.edgeSupport (L := L) (verticalLoopChain L)).card := rfl
    _ = vertCol.card := by rw [hsupport]
    _ = L := hcard

/-- The horizontal Z-row chain is a dual cycle. -/
theorem horizontalHRowChain_mem_toricDualCycles (L : ℕ) [Fact (2 ≤ L)] :
    horizontalHRowChain L ∈ Stabilizer.Lattice.toricDualCycles (L := L) := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  unfold Stabilizer.Lattice.toricDualCycles
  rw [LinearMap.mem_ker]
  ext ⟨x, y⟩
  simp only [Stabilizer.Lattice.toricDualBoundary, LinearMap.coe_mk, AddHom.coe_mk,
    horizontalHRowChain]
  by_cases hx : x = Stabilizer.Lattice.zeroCoord L
  · subst hx
    show (1 : ZMod 2) + 1 + 0 + 0 = 0
    decide
  · simp [hx]

/-- The horizontal Z-row chain is not a dual boundary (its `hRowAt` invariant is 1). -/
theorem horizontalHRowChain_not_mem_toricDualBoundaries (L : ℕ) [Fact (2 ≤ L)] :
    horizontalHRowChain L ∉ Stabilizer.Lattice.toricDualBoundaries (L := L) := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  intro h
  have h_hRowAt : Stabilizer.Lattice.hRowAt (L := L) (Stabilizer.Lattice.zeroCoord L)
      (horizontalHRowChain L) = 0 :=
    Stabilizer.Lattice.hRowAt_dualBoundary_zero (L := L)
      ⟨horizontalHRowChain L, h⟩
  have h_compute : Stabilizer.Lattice.hRowAt (L := L) (Stabilizer.Lattice.zeroCoord L)
      (horizontalHRowChain L) = 1 := by
    unfold Stabilizer.Lattice.hRowAt horizontalHRowChain
    rw [Finset.sum_eq_single (Stabilizer.Lattice.zeroCoord L)]
    · simp
    · intro b _ hbne
      simp [hbne]
    · intro hcontra; exact absurd (Finset.mem_univ _) hcontra
  rw [h_compute] at h_hRowAt
  exact absurd h_hRowAt (by decide)

/-- The horizontal Z-row chain has edge weight `L`. -/
theorem horizontalHRowChain_edgeWeight_eq_L (L : ℕ) [Fact (2 ≤ L)] :
    Stabilizer.Lattice.edgeWeight (L := L) (horizontalHRowChain L) = L := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  let z0 : Fin L := Stabilizer.Lattice.zeroCoord L
  let horizCol : Finset (Stabilizer.Lattice.EdgeIdx L) :=
    (Finset.univ.image (fun y : Fin L => Stabilizer.Lattice.EdgeIdx.h z0 y))
  have hsupport :
      Stabilizer.Lattice.edgeSupport (L := L) (horizontalHRowChain L) = horizCol := by
    ext e
    constructor
    · intro he
      have hne : horizontalHRowChain L e ≠ 0 := by
        simpa [Stabilizer.Lattice.mem_edgeSupport] using he
      cases e with
      | h x y =>
          by_cases hx : x = z0
          · subst hx
            refine Finset.mem_image.mpr ?_
            exact ⟨y, Finset.mem_univ y, rfl⟩
          · have hx' : x = z0 := by simpa [horizontalHRowChain] using hne
            exact (hx hx').elim
      | v x y => simp [horizontalHRowChain] at hne
    · intro he
      rcases Finset.mem_image.mp he with ⟨y, -, hy⟩
      subst hy
      simp [Stabilizer.Lattice.mem_edgeSupport, horizontalHRowChain, z0]
  have hinj : Function.Injective (fun y : Fin L => Stabilizer.Lattice.EdgeIdx.h z0 y) := by
    intro a b h; cases h; rfl
  have hcard : horizCol.card = L := by
    calc
      horizCol.card
          = (Finset.univ.image (fun y : Fin L => Stabilizer.Lattice.EdgeIdx.h z0 y)).card := rfl
      _ = (Finset.univ : Finset (Fin L)).card := by
          exact Finset.card_image_of_injective
            (s := (Finset.univ : Finset (Fin L)))
            (f := fun y : Fin L => Stabilizer.Lattice.EdgeIdx.h z0 y)
            (by intro a b hab; exact hinj hab)
      _ = L := by simp
  calc
    Stabilizer.Lattice.edgeWeight (L := L) (horizontalHRowChain L)
        = (Stabilizer.Lattice.edgeSupport (L := L) (horizontalHRowChain L)).card := rfl
    _ = horizCol.card := by rw [hsupport]
    _ = L := hcard

/-- The vertical X-loop operator is X-type. -/
theorem verticalLoopXOperator_isXType (L : ℕ) [Fact (0 < L)] :
    NQubitPauliGroupElement.IsXTypeElement (verticalLoopXOperator L) := by
  unfold verticalLoopXOperator NQubitPauliGroupElement.IsXTypeElement
  refine ⟨rfl, fun q => ?_⟩
  by_cases h : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧ verticalLoopChain L e = 1
  · right; simp [Stabilizer.Lattice.toricXOperatorOfChain, h]
  · left; simp [Stabilizer.Lattice.toricXOperatorOfChain, h]

/-- The horizontal Z-row operator is Z-type. -/
theorem horizontalHRowZOperator_isZType (L : ℕ) [Fact (0 < L)] :
    NQubitPauliGroupElement.IsZTypeElement (horizontalHRowZOperator L) := by
  unfold horizontalHRowZOperator NQubitPauliGroupElement.IsZTypeElement
  refine ⟨rfl, fun q => ?_⟩
  by_cases h : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧ horizontalHRowChain L e = 1
  · right; simp [Stabilizer.Lattice.toricZOperatorOfChain, h]
  · left; simp [Stabilizer.Lattice.toricZOperatorOfChain, h]

/-- The horizontal X-loop operator is X-type. -/
theorem horizontalLoopXOperator_isXType (L : ℕ) [Fact (0 < L)] :
    NQubitPauliGroupElement.IsXTypeElement (horizontalLoopXOperator L) := by
  unfold horizontalLoopXOperator NQubitPauliGroupElement.IsXTypeElement
  refine ⟨rfl, fun q => ?_⟩
  by_cases h : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧ horizontalLoopChain L e = 1
  · right; simp [Stabilizer.Lattice.toricXOperatorOfChain, h]
  · left; simp [Stabilizer.Lattice.toricXOperatorOfChain, h]

/-- The vertical V-row Z-operator is Z-type. -/
theorem verticalVRowZOperator_isZType (L : ℕ) [Fact (0 < L)] :
    NQubitPauliGroupElement.IsZTypeElement (verticalVRowZOperator L) := by
  unfold verticalVRowZOperator NQubitPauliGroupElement.IsZTypeElement
  refine ⟨rfl, fun q => ?_⟩
  by_cases h : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧ verticalVRowChain L e = 1
  · right; simp [Stabilizer.Lattice.toricZOperatorOfChain, h]
  · left; simp [Stabilizer.Lattice.toricZOperatorOfChain, h]

-- ---------------------------------------------------------------------------
-- Phase 2 / 3: Logical operators and independence
-- ---------------------------------------------------------------------------

/-- The packaged stabilizer subgroup, used to type `LogicalQubitOps`. -/
private noncomputable def packagedStabilizerGroup (L : ℕ) [Fact (2 ≤ L)] :
    StabilizerGroup (numQubits L) :=
  StabilizerGroup.mkStabilizerFromGenerators (numQubits L) (generatorsListPackaged L)
    (generators_commute_packaged L) (negIdentity_not_mem_packaged L)

/-- The packaged stabilizer group has the same toSubgroup as the canonical one. -/
private lemma packagedStabilizerGroup_toSubgroup_eq (L : ℕ) [Fact (2 ≤ L)] :
    (packagedStabilizerGroup L).toSubgroup = (stabilizerGroup L).toSubgroup := by
  show Subgroup.closure (listToSet (generatorsListPackaged L)) = _
  exact closure_packaged_eq_full L

/-- The two logical X-chains have disjoint support (one has h-edges only, the other has
v-edges only). Used to prove cross-commutation. -/
private lemma verticalLoopChain_horizontalLoopChain_supports_disjoint (L : ℕ) [Fact (0 < L)] :
    ∀ e : Stabilizer.Lattice.EdgeIdx L,
      ¬ (verticalLoopChain L e = 1 ∧ horizontalLoopChain L e = 1) := by
  intro e
  cases e with
  | h x y => simp [verticalLoopChain]
  | v x y => simp [horizontalLoopChain]

/-- Logical X for qubit 0 (`horizontalLoopX`) and logical Z for qubit 1
(`verticalVRowZ`) have disjoint supports. -/
private lemma horizontalLoopChain_verticalVRowChain_supports_disjoint (L : ℕ) [Fact (0 < L)] :
    ∀ e : Stabilizer.Lattice.EdgeIdx L,
      ¬ (horizontalLoopChain L e = 1 ∧ verticalVRowChain L e = 1) := by
  intro e
  cases e with
  | h x y => simp [verticalVRowChain]
  | v x y => simp [horizontalLoopChain]

/-- Logical Z for qubit 0 (`horizontalHRowZ`) and logical X for qubit 1
(`verticalLoopX`) have disjoint supports. -/
private lemma horizontalHRowChain_verticalLoopChain_supports_disjoint (L : ℕ) [Fact (0 < L)] :
    ∀ e : Stabilizer.Lattice.EdgeIdx L,
      ¬ (horizontalHRowChain L e = 1 ∧ verticalLoopChain L e = 1) := by
  intro e
  cases e with
  | h x y => simp [verticalLoopChain]
  | v x y => simp [horizontalHRowChain]

/-- Z-side: the two logical Z-chains have disjoint support. -/
private lemma horizontalHRowChain_verticalVRowChain_supports_disjoint (L : ℕ) [Fact (0 < L)] :
    ∀ e : Stabilizer.Lattice.EdgeIdx L,
      ¬ (horizontalHRowChain L e = 1 ∧ verticalVRowChain L e = 1) := by
  intro e
  cases e with
  | h x y => simp [verticalVRowChain]
  | v x y => simp [horizontalHRowChain]

/-- The X-operator-of-chain at qubit `q` is `X` if some edge mapping to `q` has `c e = 1`,
else `I`. -/
private lemma toricXOperatorOfChain_op_at (L : ℕ)
    (c : Stabilizer.Lattice.C1 L) (q : Fin (Stabilizer.Lattice.toricNumQubits L)) :
    (Stabilizer.Lattice.toricXOperatorOfChain L c).operators q =
      if ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧ c e = 1
        then PauliOperator.X else PauliOperator.I := rfl

/-- The Z-operator-of-chain at qubit `q`. -/
private lemma toricZOperatorOfChain_op_at (L : ℕ)
    (c : Stabilizer.Lattice.C1 L) (q : Fin (Stabilizer.Lattice.toricNumQubits L)) :
    (Stabilizer.Lattice.toricZOperatorOfChain L c).operators q =
      if ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧ c e = 1
        then PauliOperator.Z else PauliOperator.I := rfl

/-- If two chains have disjoint supports, then their Pauli operators (X-type, Z-type)
commute. -/
private lemma toricXZ_commute_of_disjoint_supports (L : ℕ) [Fact (0 < L)]
    (cX cZ : Stabilizer.Lattice.C1 L)
    (h_disj : ∀ e, ¬ (cX e = 1 ∧ cZ e = 1)) :
    Stabilizer.Lattice.toricXOperatorOfChain L cX *
        Stabilizer.Lattice.toricZOperatorOfChain L cZ =
      Stabilizer.Lattice.toricZOperatorOfChain L cZ *
        Stabilizer.Lattice.toricXOperatorOfChain L cX := by
  apply NQubitPauliGroupElement.commutes_of_componentwise_commutes
  intro q
  rw [toricXOperatorOfChain_op_at, toricZOperatorOfChain_op_at]
  by_cases hX : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧ cX e = 1
  · by_cases hZ : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧ cZ e = 1
    · -- both X and Z at q: derive contradiction from disjoint supports
      exfalso
      rcases hX with ⟨eX, hX_eq, hX_one⟩
      rcases hZ with ⟨eZ, hZ_eq, hZ_one⟩
      have h_eq : eX = eZ := Stabilizer.Lattice.edgeToQubitIdx_injective L
        (hX_eq.trans hZ_eq.symm)
      subst h_eq
      exact h_disj eX ⟨hX_one, hZ_one⟩
    · rw [if_pos hX, if_neg hZ]; rfl
  · rw [if_neg hX]
    by_cases hZ : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧ cZ e = 1
    · rw [if_pos hZ]; rfl
    · rw [if_neg hZ]

/-- Z-Z commute (both elements are Z-type). -/
private lemma horizontalHRow_verticalVRow_Z_commute (L : ℕ) [Fact (0 < L)] :
    horizontalHRowZOperator L * verticalVRowZOperator L =
      verticalVRowZOperator L * horizontalHRowZOperator L :=
  StabilizerGroup.CSSCommutationLemmas.ZType_commutes
    (horizontalHRowZOperator_isZType L) (verticalVRowZOperator_isZType L)

/-- X-X commute (both elements are X-type). -/
private lemma horizontalLoop_verticalLoop_X_commute (L : ℕ) [Fact (0 < L)] :
    horizontalLoopXOperator L * verticalLoopXOperator L =
      verticalLoopXOperator L * horizontalLoopXOperator L :=
  StabilizerGroup.CSSCommutationLemmas.XType_commutes
    (horizontalLoopXOperator_isXType L) (verticalLoopXOperator_isXType L)

/-- Cross-commutation: horizontalLoopX vs verticalVRowZ via disjoint supports. -/
private lemma horizontalLoopX_verticalVRowZ_commute (L : ℕ) [Fact (0 < L)] :
    horizontalLoopXOperator L * verticalVRowZOperator L =
      verticalVRowZOperator L * horizontalLoopXOperator L :=
  toricXZ_commute_of_disjoint_supports L (horizontalLoopChain L) (verticalVRowChain L)
    (horizontalLoopChain_verticalVRowChain_supports_disjoint L)

/-- Cross-commutation: horizontalHRowZ vs verticalLoopX via disjoint supports. -/
private lemma horizontalHRowZ_verticalLoopX_commute (L : ℕ) [Fact (0 < L)] :
    horizontalHRowZOperator L * verticalLoopXOperator L =
      verticalLoopXOperator L * horizontalHRowZOperator L := by
  have h := toricXZ_commute_of_disjoint_supports L (verticalLoopChain L)
    (horizontalHRowChain L)
    (fun e he => horizontalHRowChain_verticalLoopChain_supports_disjoint L e ⟨he.2, he.1⟩)
  -- h : verticalLoopX * horizontalHRowZ = horizontalHRowZ * verticalLoopX
  exact h.symm

/-- Anticommute: horizontalLoopX and horizontalHRowZ share exactly one edge h(0, 0). -/
private theorem horizontalLoopX_anticommute_horizontalHRowZ (L : ℕ) [Fact (2 ≤ L)] :
    NQubitPauliGroupElement.Anticommute
      (horizontalLoopXOperator L) (horizontalHRowZOperator L) := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  classical
  rw [NQubitPauliGroupElement.anticommutes_iff_odd_anticommutes]
  set z0 : Fin L := Stabilizer.Lattice.zeroCoord L with hz0
  set q0 : Fin (Stabilizer.Lattice.toricNumQubits L) :=
    Stabilizer.Lattice.edgeToQubitIdx L (Stabilizer.Lattice.EdgeIdx.h z0 z0) with hq0
  have hfilter :
      (Finset.univ.filter (NQubitPauliGroupElement.anticommutesAt
        (horizontalLoopXOperator L).operators (horizontalHRowZOperator L).operators)) =
        ({q0} : Finset (Fin (Stabilizer.Lattice.toricNumQubits L))) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_singleton, Finset.mem_univ, true_and]
    unfold NQubitPauliGroupElement.anticommutesAt
    unfold horizontalLoopXOperator horizontalHRowZOperator
    rw [toricXOperatorOfChain_op_at, toricZOperatorOfChain_op_at]
    by_cases hX : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧ horizontalLoopChain L e = 1
    · by_cases hZ : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧
          horizontalHRowChain L e = 1
      · rw [if_pos hX, if_pos hZ]
        constructor
        · intro _
          rcases hX with ⟨eX, hX_eq, hX_one⟩
          rcases hZ with ⟨eZ, hZ_eq, hZ_one⟩
          have h_eq : eX = eZ := Stabilizer.Lattice.edgeToQubitIdx_injective L
            (hX_eq.trans hZ_eq.symm)
          subst h_eq
          cases eX with
          | h x y =>
              have hy : y = z0 := by simpa [horizontalLoopChain, hz0] using hX_one
              have hx : x = z0 := by simpa [horizontalHRowChain, hz0] using hZ_one
              subst hy; subst hx
              exact hX_eq.symm
          | v x y => simp [horizontalLoopChain] at hX_one
        · intro _; decide
      · rw [if_pos hX, if_neg hZ]
        constructor
        · intro h; exact absurd h (by decide)
        · intro hq
          subst hq
          exact absurd ⟨Stabilizer.Lattice.EdgeIdx.h z0 z0, rfl,
            by simp [horizontalHRowChain, hz0]⟩ hZ
    · rw [if_neg hX]
      by_cases hZ : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧
          horizontalHRowChain L e = 1
      · rw [if_pos hZ]
        constructor
        · intro h; exact absurd h (by decide)
        · intro hq
          subst hq
          exact absurd ⟨Stabilizer.Lattice.EdgeIdx.h z0 z0, rfl,
            by simp [horizontalLoopChain, hz0]⟩ hX
      · rw [if_neg hZ]
        constructor
        · intro h; exact absurd h (by decide)
        · intro hq
          subst hq
          exact absurd ⟨Stabilizer.Lattice.EdgeIdx.h z0 z0, rfl,
            by simp [horizontalLoopChain, hz0]⟩ hX
  rw [hfilter, Finset.card_singleton]
  exact ⟨0, rfl⟩

/-- Anticommute: verticalLoopX and verticalVRowZ share exactly one edge v(0, 0). -/
private theorem verticalLoopX_anticommute_verticalVRowZ (L : ℕ) [Fact (2 ≤ L)] :
    NQubitPauliGroupElement.Anticommute
      (verticalLoopXOperator L) (verticalVRowZOperator L) := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  classical
  rw [NQubitPauliGroupElement.anticommutes_iff_odd_anticommutes]
  set z0 : Fin L := Stabilizer.Lattice.zeroCoord L with hz0
  set q0 : Fin (Stabilizer.Lattice.toricNumQubits L) :=
    Stabilizer.Lattice.edgeToQubitIdx L (Stabilizer.Lattice.EdgeIdx.v z0 z0) with hq0
  have hfilter :
      (Finset.univ.filter (NQubitPauliGroupElement.anticommutesAt
        (verticalLoopXOperator L).operators (verticalVRowZOperator L).operators)) =
        ({q0} : Finset (Fin (Stabilizer.Lattice.toricNumQubits L))) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_singleton, Finset.mem_univ, true_and]
    unfold NQubitPauliGroupElement.anticommutesAt
    unfold verticalLoopXOperator verticalVRowZOperator
    rw [toricXOperatorOfChain_op_at, toricZOperatorOfChain_op_at]
    by_cases hX : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧ verticalLoopChain L e = 1
    · by_cases hZ : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧
          verticalVRowChain L e = 1
      · rw [if_pos hX, if_pos hZ]
        constructor
        · intro _
          rcases hX with ⟨eX, hX_eq, hX_one⟩
          rcases hZ with ⟨eZ, hZ_eq, hZ_one⟩
          have h_eq : eX = eZ := Stabilizer.Lattice.edgeToQubitIdx_injective L
            (hX_eq.trans hZ_eq.symm)
          subst h_eq
          cases eX with
          | h x y => simp [verticalLoopChain] at hX_one
          | v x y =>
              have hx : x = z0 := by simpa [verticalLoopChain, hz0] using hX_one
              have hy : y = z0 := by simpa [verticalVRowChain, hz0] using hZ_one
              subst hx; subst hy
              exact hX_eq.symm
        · intro _; decide
      · rw [if_pos hX, if_neg hZ]
        constructor
        · intro h; exact absurd h (by decide)
        · intro hq
          subst hq
          exact absurd ⟨Stabilizer.Lattice.EdgeIdx.v z0 z0, rfl,
            by simp [verticalVRowChain, hz0]⟩ hZ
    · rw [if_neg hX]
      by_cases hZ : ∃ e, Stabilizer.Lattice.edgeToQubitIdx L e = q ∧
          verticalVRowChain L e = 1
      · rw [if_pos hZ]
        constructor
        · intro h; exact absurd h (by decide)
        · intro hq
          subst hq
          exact absurd ⟨Stabilizer.Lattice.EdgeIdx.v z0 z0, rfl,
            by simp [verticalLoopChain, hz0]⟩ hX
      · rw [if_neg hZ]
        constructor
        · intro h; exact absurd h (by decide)
        · intro hq
          subst hq
          exact absurd ⟨Stabilizer.Lattice.EdgeIdx.v z0 z0, rfl,
            by simp [verticalLoopChain, hz0]⟩ hX
  rw [hfilter, Finset.card_singleton]
  exact ⟨0, rfl⟩

/-- Centralizer membership: horizontalLoopX in centralizer of packaged stabilizer. -/
private theorem horizontalLoopXOperator_mem_centralizer (L : ℕ) [Fact (2 ≤ L)] :
    horizontalLoopXOperator L ∈ StabilizerGroup.centralizer (packagedStabilizerGroup L) := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  rw [StabilizerGroup.centralizer_eq_of_toSubgroup_eq _ (stabilizerGroup L)
    (packagedStabilizerGroup_toSubgroup_eq L)]
  exact (Stabilizer.Lattice.toricXOperatorOfChain_mem_centralizer_iff_cycle L
    (horizontalLoopChain L)).mpr (horizontalLoopChain_mem_toricCycles L)

/-- Centralizer membership: verticalLoopX in centralizer of packaged stabilizer. -/
private theorem verticalLoopXOperator_mem_centralizer (L : ℕ) [Fact (2 ≤ L)] :
    verticalLoopXOperator L ∈ StabilizerGroup.centralizer (packagedStabilizerGroup L) := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  rw [StabilizerGroup.centralizer_eq_of_toSubgroup_eq _ (stabilizerGroup L)
    (packagedStabilizerGroup_toSubgroup_eq L)]
  exact (Stabilizer.Lattice.toricXOperatorOfChain_mem_centralizer_iff_cycle L
    (verticalLoopChain L)).mpr (verticalLoopChain_mem_toricCycles L)

/-- Centralizer membership: horizontalHRowZ in centralizer of packaged stabilizer. -/
private theorem horizontalHRowZOperator_mem_centralizer (L : ℕ) [Fact (2 ≤ L)] :
    horizontalHRowZOperator L ∈ StabilizerGroup.centralizer (packagedStabilizerGroup L) := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  rw [StabilizerGroup.centralizer_eq_of_toSubgroup_eq _ (stabilizerGroup L)
    (packagedStabilizerGroup_toSubgroup_eq L)]
  exact (Stabilizer.Lattice.toricZOperatorOfChain_mem_centralizer_iff_dualCycle L
    (horizontalHRowChain L)).mpr (horizontalHRowChain_mem_toricDualCycles L)

/-- Centralizer membership: verticalVRowZ in centralizer of packaged stabilizer. -/
private theorem verticalVRowZOperator_mem_centralizer (L : ℕ) [Fact (2 ≤ L)] :
    verticalVRowZOperator L ∈ StabilizerGroup.centralizer (packagedStabilizerGroup L) := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  rw [StabilizerGroup.centralizer_eq_of_toSubgroup_eq _ (stabilizerGroup L)
    (packagedStabilizerGroup_toSubgroup_eq L)]
  exact (Stabilizer.Lattice.toricZOperatorOfChain_mem_centralizer_iff_dualCycle L
    (verticalVRowChain L)).mpr (verticalVRowChain_mem_toricDualCycles L)

/-- LogicalQubitOps for logical qubit 0: (horizontalLoopX, horizontalHRowZ). -/
private noncomputable def logicalQubit0 (L : ℕ) [Fact (2 ≤ L)] :
    LogicalQubitOps (numQubits L) (packagedStabilizerGroup L) where
  xOp := horizontalLoopXOperator L
  zOp := horizontalHRowZOperator L
  x_mem_centralizer := horizontalLoopXOperator_mem_centralizer L
  z_mem_centralizer := horizontalHRowZOperator_mem_centralizer L
  anticommute := horizontalLoopX_anticommute_horizontalHRowZ L

/-- LogicalQubitOps for logical qubit 1: (verticalLoopX, verticalVRowZ). -/
private noncomputable def logicalQubit1 (L : ℕ) [Fact (2 ≤ L)] :
    LogicalQubitOps (numQubits L) (packagedStabilizerGroup L) where
  xOp := verticalLoopXOperator L
  zOp := verticalVRowZOperator L
  x_mem_centralizer := verticalLoopXOperator_mem_centralizer L
  z_mem_centralizer := verticalVRowZOperator_mem_centralizer L
  anticommute := verticalLoopX_anticommute_verticalVRowZ L

/-- Logical operator data for the toric code. -/
private noncomputable def toric_logicalOps (L : ℕ) [Fact (2 ≤ L)] :
    Fin 2 → LogicalQubitOps (numQubits L) (packagedStabilizerGroup L)
  | ⟨0, _⟩ => logicalQubit0 L
  | ⟨1, _⟩ => logicalQubit1 L

private lemma toric_logicalOps_zero (L : ℕ) [Fact (2 ≤ L)] :
    toric_logicalOps L 0 = logicalQubit0 L := rfl

private lemma toric_logicalOps_one (L : ℕ) [Fact (2 ≤ L)] :
    toric_logicalOps L 1 = logicalQubit1 L := rfl

set_option maxHeartbeats 800000 in
/-- Cross-commutation of the logical operators. -/
private theorem toric_logical_commute_cross (L : ℕ) [Fact (2 ≤ L)] :
    ∀ ℓ ℓ', ℓ ≠ ℓ' →
      ((toric_logicalOps L ℓ).xOp * (toric_logicalOps L ℓ').xOp =
          (toric_logicalOps L ℓ').xOp * (toric_logicalOps L ℓ).xOp ∧
        (toric_logicalOps L ℓ).xOp * (toric_logicalOps L ℓ').zOp =
          (toric_logicalOps L ℓ').zOp * (toric_logicalOps L ℓ).xOp ∧
        (toric_logicalOps L ℓ).zOp * (toric_logicalOps L ℓ').xOp =
          (toric_logicalOps L ℓ').xOp * (toric_logicalOps L ℓ).zOp ∧
        (toric_logicalOps L ℓ).zOp * (toric_logicalOps L ℓ').zOp =
          (toric_logicalOps L ℓ').zOp * (toric_logicalOps L ℓ).zOp) := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  -- Hardcode the (0, 1) case using the explicit logicalQubit0/1 definitions.
  have h_01 :
      ((logicalQubit0 L).xOp * (logicalQubit1 L).xOp =
            (logicalQubit1 L).xOp * (logicalQubit0 L).xOp ∧
        (logicalQubit0 L).xOp * (logicalQubit1 L).zOp =
            (logicalQubit1 L).zOp * (logicalQubit0 L).xOp ∧
        (logicalQubit0 L).zOp * (logicalQubit1 L).xOp =
            (logicalQubit1 L).xOp * (logicalQubit0 L).zOp ∧
        (logicalQubit0 L).zOp * (logicalQubit1 L).zOp =
            (logicalQubit1 L).zOp * (logicalQubit0 L).zOp) := by
    refine ⟨horizontalLoop_verticalLoop_X_commute L, ?_, ?_,
      horizontalHRow_verticalVRow_Z_commute L⟩
    · exact horizontalLoopX_verticalVRowZ_commute L
    · exact horizontalHRowZ_verticalLoopX_commute L
  intro ℓ ℓ' hne
  have hℓ := Fin.exists_fin_two.mp ⟨ℓ, rfl⟩
  have hℓ' := Fin.exists_fin_two.mp ⟨ℓ', rfl⟩
  rcases hℓ with hℓ0 | hℓ1
  · rcases hℓ' with hℓ'0 | hℓ'1
    · exact absurd (hℓ0.trans hℓ'0.symm) hne
    · -- ℓ = 0, ℓ' = 1
      rw [hℓ0, hℓ'1, toric_logicalOps_zero, toric_logicalOps_one]
      exact h_01
  · rcases hℓ' with hℓ'0 | hℓ'1
    · -- ℓ = 1, ℓ' = 0
      rw [hℓ1, hℓ'0, toric_logicalOps_zero, toric_logicalOps_one]
      refine ⟨h_01.1.symm, h_01.2.2.1.symm, h_01.2.1.symm, h_01.2.2.2.symm⟩
    · exact absurd (hℓ1.trans hℓ'1.symm) hne

-- ---------------------------------------------------------------------------
-- Phase 3.B: Edge ↔ qubit bijection
-- ---------------------------------------------------------------------------

/-- Cardinality match: `card(EdgeIdx L) = numQubits L = 2L²`. -/
private lemma card_edgeIdx_eq_numQubits (L : ℕ) :
    Fintype.card (Stabilizer.Lattice.EdgeIdx L) = numQubits L := by
  simp [numQubits]

/-- `edgeToQubitIdx` is a bijection (injection between equal-size finite types). -/
private lemma edgeToQubitIdx_bijective (L : ℕ) [Fact (0 < L)] :
    Function.Bijective (Stabilizer.Lattice.edgeToQubitIdx L) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨Stabilizer.Lattice.edgeToQubitIdx_injective L, ?_⟩
  simp [numQubits, Stabilizer.Lattice.toricNumQubits]

/-- The right-inverse of `edgeToQubitIdx`: maps a qubit back to its edge. -/
private noncomputable def qubitToEdgeIdx (L : ℕ) [Fact (0 < L)] :
    Fin (numQubits L) → Stabilizer.Lattice.EdgeIdx L :=
  Function.surjInv (edgeToQubitIdx_bijective L).2

private lemma edgeToQubitIdx_qubitToEdgeIdx (L : ℕ) [Fact (0 < L)]
    (q : Fin (numQubits L)) :
    Stabilizer.Lattice.edgeToQubitIdx L (qubitToEdgeIdx L q) = q :=
  Function.surjInv_eq (edgeToQubitIdx_bijective L).2 q

private lemma qubitToEdgeIdx_edgeToQubitIdx (L : ℕ) [Fact (0 < L)]
    (e : Stabilizer.Lattice.EdgeIdx L) :
    qubitToEdgeIdx L (Stabilizer.Lattice.edgeToQubitIdx L e) = e := by
  apply (edgeToQubitIdx_bijective L).1
  exact edgeToQubitIdx_qubitToEdgeIdx L (Stabilizer.Lattice.edgeToQubitIdx L e)

-- ---------------------------------------------------------------------------
-- Phase 3.C: Symplectic-half identification lemmas
-- ---------------------------------------------------------------------------

/-- Helper: a `ZMod 2` value is either `0` or `1`. -/
private lemma zmod2_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  rcases Fin.exists_fin_two.mp ⟨a, rfl⟩ with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- Z-type elements have X-half symplectic component identically zero. -/
private lemma toSymplectic_ZType_X_zero {n : ℕ}
    (g : NQubitPauliGroupElement n) (hg : NQubitPauliGroupElement.IsZTypeElement g)
    (i : Fin n) :
    NQubitPauliOperator.toSymplectic g.operators (Fin.castAdd n i) = 0 := by
  rw [NQubitPauliOperator.toSymplectic_X_part]
  rcases hg.2 i with hI | hZ
  · rw [hI]; rfl
  · rw [hZ]; rfl

/-- X-type elements have Z-half symplectic component identically zero. -/
private lemma toSymplectic_XType_Z_zero {n : ℕ}
    (g : NQubitPauliGroupElement n) (hg : NQubitPauliGroupElement.IsXTypeElement g)
    (i : Fin n) :
    NQubitPauliOperator.toSymplectic g.operators (Fin.natAdd n i) = 0 := by
  rw [NQubitPauliOperator.toSymplectic_Z_part]
  rcases hg.2 i with hI | hX
  · rw [hI]; rfl
  · rw [hX]; rfl

/-- The Z-half symplectic value of `vertexStab L x y` at qubit `i` equals
`cutMap(singleVtx (x,y))` evaluated at the edge corresponding to `i`. -/
private lemma toSymplectic_vertexStab_Z_eq (L : ℕ) [Fact (2 ≤ L)]
    (p : Fin L × Fin L) (i : Fin (numQubits L)) :
    NQubitPauliOperator.toSymplectic (vertexStab L p.1 p.2).operators
        (Fin.natAdd (numQubits L) i) =
      Stabilizer.Lattice.toricVertexCutMap (L := L)
        (Stabilizer.Lattice.singleVtx p) (qubitToEdgeIdx L i) := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  rw [NQubitPauliOperator.toSymplectic_Z_part]
  rw [show vertexStab L p.1 p.2 = Stabilizer.Lattice.toricZOperatorOfChain L
        (Stabilizer.Lattice.toricVertexCutMap (L := L) (Stabilizer.Lattice.singleVtx p)) from
    (Stabilizer.Lattice.toricZOperatorOfChain_cutMap_singleVtx L p.1 p.2).symm]
  rw [toricZOperatorOfChain_op_at]
  set v := Stabilizer.Lattice.toricVertexCutMap (L := L)
    (Stabilizer.Lattice.singleVtx p) (qubitToEdgeIdx L i) with hv
  rcases zmod2_zero_or_one v with h0 | h1
  · -- v = 0: no edge index has chain value 1 at i; symplectic = 0.
    rw [if_neg ?_]
    · rw [h0]; rfl
    · rintro ⟨e', heq, hone⟩
      -- e' = qubitToEdgeIdx L i (by injectivity), so v = chain at e' = 1 ≠ 0
      have h_inj : e' = qubitToEdgeIdx L i := by
        apply (edgeToQubitIdx_bijective L).1
        rw [heq, edgeToQubitIdx_qubitToEdgeIdx]
      rw [← h_inj] at hv
      rw [hv] at h0
      exact absurd hone (h0 ▸ (by decide : (0 : ZMod 2) ≠ 1))
  · -- v = 1: edge `qubitToEdgeIdx L i` has chain value 1; symplectic = 1.
    rw [if_pos ?_]
    · rw [h1]; rfl
    · refine ⟨qubitToEdgeIdx L i, edgeToQubitIdx_qubitToEdgeIdx L i, ?_⟩
      rw [← hv]; exact h1

/-- The X-half symplectic value of `faceStab L x y` at qubit `i` equals
`boundary2(singleFace (x,y))` evaluated at the edge corresponding to `i`. -/
private lemma toSymplectic_faceStab_X_eq (L : ℕ) [Fact (2 ≤ L)]
    (p : Fin L × Fin L) (i : Fin (numQubits L)) :
    NQubitPauliOperator.toSymplectic (faceStab L p.1 p.2).operators
        (Fin.castAdd (numQubits L) i) =
      Stabilizer.Lattice.toricBoundary2 (L := L)
        (Stabilizer.Lattice.singleFace p) (qubitToEdgeIdx L i) := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  rw [NQubitPauliOperator.toSymplectic_X_part]
  rw [show faceStab L p.1 p.2 = Stabilizer.Lattice.toricXOperatorOfChain L
        (Stabilizer.Lattice.toricBoundary2 (L := L) (Stabilizer.Lattice.singleFace p)) from
    (Stabilizer.Lattice.toricXOperatorOfChain_boundary_singleFace L p.1 p.2).symm]
  rw [toricXOperatorOfChain_op_at]
  set v := Stabilizer.Lattice.toricBoundary2 (L := L)
    (Stabilizer.Lattice.singleFace p) (qubitToEdgeIdx L i) with hv
  rcases zmod2_zero_or_one v with h0 | h1
  · rw [if_neg ?_]
    · rw [h0]; rfl
    · rintro ⟨e', heq, hone⟩
      have h_inj : e' = qubitToEdgeIdx L i := by
        apply (edgeToQubitIdx_bijective L).1
        rw [heq, edgeToQubitIdx_qubitToEdgeIdx]
      rw [← h_inj] at hv
      rw [hv] at h0
      exact absurd hone (h0 ▸ (by decide : (0 : ZMod 2) ≠ 1))
  · rw [if_pos ?_]
    · rw [h1]; rfl
    · refine ⟨qubitToEdgeIdx L i, edgeToQubitIdx_qubitToEdgeIdx L i, ?_⟩
      rw [← hv]; exact h1

-- ---------------------------------------------------------------------------
-- Phase 3.D: Indexing lemmas for generatorsListPackaged
-- ---------------------------------------------------------------------------

/-- Length of the Z-trimmed list equals coordsTrimmed length. -/
private lemma generatorsListZTrimmed_length (L : ℕ) [Fact (0 < L)] :
    (generatorsListZTrimmed L).length = (coordsTrimmed L).length := by
  simp [generatorsListZTrimmed]

/-- Length of the X-trimmed list equals coordsTrimmed length. -/
private lemma generatorsListXTrimmed_length (L : ℕ) [Fact (0 < L)] :
    (generatorsListXTrimmed L).length = (coordsTrimmed L).length := by
  simp [generatorsListXTrimmed]

/-- The packaged list at a Z-block index equals a vertex stab. -/
private lemma get_packaged_Z (L : ℕ) [Fact (0 < L)]
    (k : Fin (coordsTrimmed L).length)
    (hk : k.val < (generatorsListPackaged L).length) :
    (generatorsListPackaged L).get ⟨k.val, hk⟩ =
      vertexStab L ((coordsTrimmed L).get k).1 ((coordsTrimmed L).get k).2 := by
  show (generatorsListZTrimmed L ++ generatorsListXTrimmed L).get ⟨k.val, hk⟩ = _
  have h_lt : k.val < (generatorsListZTrimmed L).length := by
    rw [generatorsListZTrimmed_length]; exact k.isLt
  rw [List.get_eq_getElem, List.getElem_append_left h_lt]
  show (generatorsListZTrimmed L)[k.val]'h_lt = _
  unfold generatorsListZTrimmed
  rw [List.getElem_map]
  rfl

/-- The packaged list at an X-block index `j` (with `j ≥ nZ`) equals a face stab at
the `(j - nZ)`-th trimmed coord. -/
private lemma get_packaged_X (L : ℕ) [Fact (0 < L)]
    (j : ℕ) (hj : j < (generatorsListPackaged L).length)
    (hge : (coordsTrimmed L).length ≤ j)
    (hsub : j - (coordsTrimmed L).length < (coordsTrimmed L).length) :
    (generatorsListPackaged L).get ⟨j, hj⟩ =
      faceStab L ((coordsTrimmed L)[j - (coordsTrimmed L).length]'hsub).1
                 ((coordsTrimmed L)[j - (coordsTrimmed L).length]'hsub).2 := by
  show (generatorsListZTrimmed L ++ generatorsListXTrimmed L).get ⟨j, hj⟩ = _
  have hZge : (generatorsListZTrimmed L).length ≤ j := by
    rw [generatorsListZTrimmed_length]; exact hge
  rw [List.get_eq_getElem, List.getElem_append_right hZge]
  -- Goal: (generatorsListXTrimmed L)[j - (generatorsListZTrimmed L).length]'_ = _
  unfold generatorsListXTrimmed
  rw [List.getElem_map]
  -- Goal: faceStab L (coordsTrimmed L)[j - (generatorsListZTrimmed L).length].1 ... = ...
  --     where the LHS index has subtraction by generatorsListZTrimmed.length
  --     and the RHS by (coordsTrimmed L).length.
  -- These are equal due to generatorsListZTrimmed_length.
  congr 2 <;>
    (simp only [show (generatorsListZTrimmed L).length = (coordsTrimmed L).length from
      generatorsListZTrimmed_length L])

-- ---------------------------------------------------------------------------
-- Phase 3.E: Block kernel-collapse lemmas
-- ---------------------------------------------------------------------------

/-- `coordsTrimmed L` is `Nodup`. -/
private lemma coordsTrimmed_nodup (L : ℕ) [Fact (0 < L)] :
    (coordsTrimmed L).Nodup := by
  unfold coordsTrimmed
  apply List.Nodup.filter
  show ((List.finRange L).product (List.finRange L)).Nodup
  exact List.Nodup.product (List.nodup_finRange L) (List.nodup_finRange L)

/-- `coordsTrimmed L` does not contain the origin. -/
private lemma coordsTrimmed_not_mem_origin (L : ℕ) [Fact (0 < L)] :
    originCoord L ∉ coordsTrimmed L := by
  intro h
  unfold coordsTrimmed at h
  rcases List.mem_filter.mp h with ⟨_, h2⟩
  simp at h2

/-- Vertex-side block kernel collapse: a linear combination of `singleVtx` over the
trimmed coords whose `cutMap` is `0` must have all-zero coefficients. -/
private lemma trimmed_combo_singleVtx_eq_zero (L : ℕ) [Fact (0 < L)]
    (c : Fin (coordsTrimmed L).length → ZMod 2)
    (hker : (∑ i, c i • Stabilizer.Lattice.singleVtx (L := L) ((coordsTrimmed L).get i)) ∈
        LinearMap.ker (Stabilizer.Lattice.toricVertexCutMap (L := L))) :
    ∀ i, c i = 0 := by
  classical
  rw [Stabilizer.Lattice.mem_ker_cutMap_iff] at hker
  obtain ⟨k, hk⟩ := hker
  -- Evaluate at origin: sum is 0 (origin ∉ trimmed), so k = 0.
  have h_orig : (∑ i, c i • Stabilizer.Lattice.singleVtx (L := L)
      ((coordsTrimmed L).get i)) (originCoord L) = 0 := by
    rw [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    have h_get_ne : (coordsTrimmed L).get i ≠ originCoord L := by
      have := List.get_mem (coordsTrimmed L) i
      intro heq
      rw [heq] at this
      exact coordsTrimmed_not_mem_origin L this
    show c i * Stabilizer.Lattice.singleVtx (L := L) ((coordsTrimmed L).get i)
        (originCoord L) = 0
    rw [Stabilizer.Lattice.singleVtx_apply_ne (Ne.symm h_get_ne)]
    ring
  have hk_zero : k = 0 := by
    have := congr_fun hk (originCoord L)
    rw [h_orig] at this
    exact this.symm
  -- So the sum is identically 0.
  have h_sum_zero : (∑ i, c i • Stabilizer.Lattice.singleVtx (L := L)
      ((coordsTrimmed L).get i)) = 0 := by
    rw [hk]; ext; simp [hk_zero]
  -- Extract each c j = 0 by evaluating at (coordsTrimmed L).get j.
  intro j
  have h_at_j : (∑ i, c i • Stabilizer.Lattice.singleVtx (L := L)
      ((coordsTrimmed L).get i)) ((coordsTrimmed L).get j) = 0 := by
    rw [h_sum_zero]; rfl
  rw [Finset.sum_apply] at h_at_j
  rw [Finset.sum_eq_single j] at h_at_j
  · show c j = 0
    have : c j * Stabilizer.Lattice.singleVtx (L := L) ((coordsTrimmed L).get j)
        ((coordsTrimmed L).get j) = 0 := h_at_j
    rw [Stabilizer.Lattice.singleVtx_apply_self] at this
    simpa using this
  · intro i _ hij
    have hne : (coordsTrimmed L).get i ≠ (coordsTrimmed L).get j := by
      intro heq
      exact hij (List.nodup_iff_injective_get.mp (coordsTrimmed_nodup L) heq)
    show c i * Stabilizer.Lattice.singleVtx (L := L) ((coordsTrimmed L).get i)
        ((coordsTrimmed L).get j) = 0
    rw [Stabilizer.Lattice.singleVtx_apply_ne (Ne.symm hne)]
    ring
  · intro hcontra; exact absurd (Finset.mem_univ j) hcontra

/-- Face-side block kernel collapse: same as Z-side but for `singleFace` and `boundary2`. -/
private lemma trimmed_combo_singleFace_eq_zero (L : ℕ) [Fact (0 < L)]
    (c : Fin (coordsTrimmed L).length → ZMod 2)
    (hker : (∑ i, c i • Stabilizer.Lattice.singleFace (L := L) ((coordsTrimmed L).get i)) ∈
        LinearMap.ker (Stabilizer.Lattice.toricBoundary2 (L := L))) :
    ∀ i, c i = 0 := by
  classical
  rw [Stabilizer.Lattice.mem_ker_boundary2_iff] at hker
  obtain ⟨k, hk⟩ := hker
  have h_orig : (∑ i, c i • Stabilizer.Lattice.singleFace (L := L)
      ((coordsTrimmed L).get i)) (originCoord L) = 0 := by
    rw [Finset.sum_apply]
    apply Finset.sum_eq_zero
    intro i _
    have h_get_ne : (coordsTrimmed L).get i ≠ originCoord L := by
      have := List.get_mem (coordsTrimmed L) i
      intro heq
      rw [heq] at this
      exact coordsTrimmed_not_mem_origin L this
    show c i * Stabilizer.Lattice.singleFace (L := L) ((coordsTrimmed L).get i)
        (originCoord L) = 0
    rw [Stabilizer.Lattice.singleFace_apply_ne (Ne.symm h_get_ne)]
    ring
  have hk_zero : k = 0 := by
    have := congr_fun hk (originCoord L)
    rw [h_orig] at this
    exact this.symm
  have h_sum_zero : (∑ i, c i • Stabilizer.Lattice.singleFace (L := L)
      ((coordsTrimmed L).get i)) = 0 := by
    rw [hk]; ext; simp [hk_zero]
  intro j
  have h_at_j : (∑ i, c i • Stabilizer.Lattice.singleFace (L := L)
      ((coordsTrimmed L).get i)) ((coordsTrimmed L).get j) = 0 := by
    rw [h_sum_zero]; rfl
  rw [Finset.sum_apply] at h_at_j
  rw [Finset.sum_eq_single j] at h_at_j
  · have : c j * Stabilizer.Lattice.singleFace (L := L) ((coordsTrimmed L).get j)
        ((coordsTrimmed L).get j) = 0 := h_at_j
    rw [Stabilizer.Lattice.singleFace_apply_self] at this
    simpa using this
  · intro i _ hij
    have hne : (coordsTrimmed L).get i ≠ (coordsTrimmed L).get j := by
      intro heq
      exact hij (List.nodup_iff_injective_get.mp (coordsTrimmed_nodup L) heq)
    show c i * Stabilizer.Lattice.singleFace (L := L) ((coordsTrimmed L).get i)
        ((coordsTrimmed L).get j) = 0
    rw [Stabilizer.Lattice.singleFace_apply_ne (Ne.symm hne)]
    ring
  · intro hcontra; exact absurd (Finset.mem_univ j) hcontra

-- ---------------------------------------------------------------------------
-- Phase 3.F: Main theorem
-- ---------------------------------------------------------------------------

/-- Symplectic linear independence of the trimmed generator list. -/
private theorem rowsLinearIndependent_generatorsListPackaged (L : ℕ) [Fact (2 ≤ L)] :
    NQubitPauliGroupElement.rowsLinearIndependent (generatorsListPackaged L) := by
  haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
  unfold NQubitPauliGroupElement.rowsLinearIndependent
  rw [Fintype.linearIndependent_iff]
  intro f hsum j
  -- hsum : ∑ k, f k • checkMatrix _ k = 0
  -- (this is a function equation in Fin (numQubits L + numQubits L) → ZMod 2)
  -- Step 1: the Z-block coefficients (j.val < L²-1) vanish via Z-half columns.
  -- Step 2: the X-block coefficients (j.val ≥ L²-1) vanish via X-half columns.
  -- Define the Z-block coefficient function
  let cZ : Fin (coordsTrimmed L).length → ZMod 2 := fun i =>
    f ⟨i.val, by
      have : (coordsTrimmed L).length ≤ (generatorsListPackaged L).length := by
        unfold generatorsListPackaged
        rw [List.length_append]
        simp [generatorsListZTrimmed]
      omega⟩
  -- The Z-half of the sum at each edge yields the chain combination.
  have h_chain_Z : (∑ i, cZ i • Stabilizer.Lattice.singleVtx (L := L)
      ((coordsTrimmed L).get i)) ∈
      LinearMap.ker (Stabilizer.Lattice.toricVertexCutMap (L := L)) := by
    rw [LinearMap.mem_ker]
    ext e
    -- Specialize hsum at column Fin.natAdd (numQubits L) (edgeToQubitIdx L e).
    have h_col := congr_fun hsum (Fin.natAdd (numQubits L)
      (Stabilizer.Lattice.edgeToQubitIdx L e))
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h_col
    -- Reindex via Fin (n+m) ≃ Fin n ⊕ Fin m.
    -- Total length = 2 * (coordsTrimmed L).length.
    have hlen : (generatorsListPackaged L).length =
        (coordsTrimmed L).length + (coordsTrimmed L).length := by
      unfold generatorsListPackaged
      rw [List.length_append]
      simp [generatorsListZTrimmed, generatorsListXTrimmed]
    have hsum_split :
        ∑ k : Fin (generatorsListPackaged L).length,
          f k * NQubitPauliGroupElement.checkMatrix (generatorsListPackaged L) k
            (Fin.natAdd (numQubits L) (Stabilizer.Lattice.edgeToQubitIdx L e)) =
        ∑ k : Fin (coordsTrimmed L).length,
          f ⟨k.val, by have := k.isLt; omega⟩ *
            NQubitPauliGroupElement.checkMatrix (generatorsListPackaged L)
              ⟨k.val, by have := k.isLt; omega⟩
              (Fin.natAdd (numQubits L) (Stabilizer.Lattice.edgeToQubitIdx L e)) := by
      -- The X-block rows (k.val ≥ trimmed.length) contribute 0 in the Z-half.
      let nZ := (coordsTrimmed L).length
      have hpartition : (Finset.univ : Finset (Fin (generatorsListPackaged L).length)) =
          (Finset.univ.filter (fun k => k.val < nZ)) ∪
          (Finset.univ.filter (fun k => ¬ k.val < nZ)) := by
        rw [Finset.filter_union_filter_neg_eq]
      have hdisj : Disjoint
          ((Finset.univ : Finset (Fin (generatorsListPackaged L).length)).filter (fun k => k.val < nZ))
          (Finset.univ.filter (fun k => ¬ k.val < nZ)) :=
        Finset.disjoint_filter_filter_neg _ _ _
      rw [hpartition, Finset.sum_union hdisj]
      -- The "right" sum (X-block) is 0.
      have hX_zero : ∑ k ∈ (Finset.univ : Finset (Fin (generatorsListPackaged L).length)).filter
          (fun k => ¬ k.val < nZ),
          f k * NQubitPauliGroupElement.checkMatrix (generatorsListPackaged L) k
            (Fin.natAdd (numQubits L) (Stabilizer.Lattice.edgeToQubitIdx L e)) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [Finset.mem_filter] at hk
        have hk_ge : nZ ≤ k.val := Nat.le_of_not_lt hk.2
        have hk_sub : k.val - nZ < nZ := by have := k.isLt; omega
        have hp_eq := get_packaged_X L k.val k.isLt hk_ge hk_sub
        set p := (coordsTrimmed L)[k.val - nZ]'hk_sub with hp_def
        unfold NQubitPauliGroupElement.checkMatrix
        rw [show k = ⟨k.val, k.isLt⟩ from rfl, hp_eq]
        rw [toSymplectic_XType_Z_zero (faceStab L p.1 p.2) (faceStab_is_XType L p.1 p.2)]
        ring
      rw [hX_zero, add_zero]
      -- Convert the Z-block sum (filter by k.val < nZ) to a sum over Fin nZ.
      apply Finset.sum_bij (fun (k : Fin (generatorsListPackaged L).length)
        (hk : k ∈ (Finset.univ : Finset (Fin (generatorsListPackaged L).length)).filter
          (fun k => k.val < nZ)) => (⟨k.val, (Finset.mem_filter.mp hk).2⟩ : Fin nZ))
      · intros; exact Finset.mem_univ _
      · intros a ha b hb hab
        rcases a with ⟨a, ha2⟩; rcases b with ⟨b, hb2⟩
        simp at hab
        exact Fin.ext hab
      · intros b _
        refine ⟨⟨b.val, ?_⟩, ?_, by simp [Fin.ext_iff]⟩
        · have hb_lt := b.isLt
          have : nZ + nZ = (generatorsListPackaged L).length := hlen.symm
          omega
        · rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, b.isLt⟩
      · intro a ha
        rfl
    rw [hsum_split] at h_col
    -- Now h_col equates the Z-block sum (over Fin nZ) at the Z-half column to 0.
    -- Convert checkMatrix entries to chain values via toSymplectic_vertexStab_Z_eq.
    have h_eq : ∀ k : Fin (coordsTrimmed L).length,
        NQubitPauliGroupElement.checkMatrix (generatorsListPackaged L)
          ⟨k.val, by have := k.isLt; omega⟩
          (Fin.natAdd (numQubits L) (Stabilizer.Lattice.edgeToQubitIdx L e)) =
        Stabilizer.Lattice.toricVertexCutMap (L := L)
          (Stabilizer.Lattice.singleVtx (L := L) ((coordsTrimmed L).get k)) e := by
      intro k
      have hp_eq := get_packaged_Z L k (by have := k.isLt; omega)
      unfold NQubitPauliGroupElement.checkMatrix
      rw [hp_eq, toSymplectic_vertexStab_Z_eq, qubitToEdgeIdx_edgeToQubitIdx]
    have h_col' : ∑ k : Fin (coordsTrimmed L).length, cZ k *
        Stabilizer.Lattice.toricVertexCutMap (L := L)
          (Stabilizer.Lattice.singleVtx (L := L) ((coordsTrimmed L).get k)) e = 0 := by
      rw [← h_col]
      apply Finset.sum_congr rfl
      intro k _
      rw [h_eq]
    -- Goal: (toricVertexCutMap (∑ i, cZ i • singleVtx ...)) e = 0
    rw [map_sum]
    rw [Finset.sum_apply]
    convert h_col' using 1
    apply Finset.sum_congr rfl
    intro k _
    rw [LinearMap.map_smul]
    show cZ k • Stabilizer.Lattice.toricVertexCutMap (L := L)
        (Stabilizer.Lattice.singleVtx (L := L) ((coordsTrimmed L).get k)) e =
      cZ k * Stabilizer.Lattice.toricVertexCutMap (L := L)
        (Stabilizer.Lattice.singleVtx (L := L) ((coordsTrimmed L).get k)) e
    rw [smul_eq_mul]
  -- Now apply Z-block kernel collapse to get cZ = 0.
  have hZ_zero : ∀ i, cZ i = 0 := trimmed_combo_singleVtx_eq_zero L cZ h_chain_Z
  -- Symmetric: define cX and apply face-side kernel collapse.
  let cX : Fin (coordsTrimmed L).length → ZMod 2 := fun i =>
    f ⟨(coordsTrimmed L).length + i.val, by
      have hlen : (generatorsListPackaged L).length =
          (coordsTrimmed L).length + (coordsTrimmed L).length := by
        unfold generatorsListPackaged
        rw [List.length_append]
        simp [generatorsListZTrimmed, generatorsListXTrimmed]
      have := i.isLt
      omega⟩
  have h_chain_X : (∑ i, cX i • Stabilizer.Lattice.singleFace (L := L)
      ((coordsTrimmed L).get i)) ∈
      LinearMap.ker (Stabilizer.Lattice.toricBoundary2 (L := L)) := by
    rw [LinearMap.mem_ker]
    ext e
    have h_col := congr_fun hsum (Fin.castAdd (numQubits L)
      (Stabilizer.Lattice.edgeToQubitIdx L e))
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h_col
    let nZ := (coordsTrimmed L).length
    have hlen : (generatorsListPackaged L).length = nZ + nZ := by
      unfold generatorsListPackaged
      rw [List.length_append, generatorsListZTrimmed_length, generatorsListXTrimmed_length]
    have hsum_split :
        ∑ k : Fin (generatorsListPackaged L).length,
          f k * NQubitPauliGroupElement.checkMatrix (generatorsListPackaged L) k
            (Fin.castAdd (numQubits L) (Stabilizer.Lattice.edgeToQubitIdx L e)) =
        ∑ k : Fin (coordsTrimmed L).length,
          f ⟨nZ + k.val, by have := k.isLt; omega⟩ *
            NQubitPauliGroupElement.checkMatrix (generatorsListPackaged L)
              ⟨nZ + k.val, by have := k.isLt; omega⟩
              (Fin.castAdd (numQubits L) (Stabilizer.Lattice.edgeToQubitIdx L e)) := by
      have hpartition : (Finset.univ : Finset (Fin (generatorsListPackaged L).length)) =
          (Finset.univ.filter (fun k => k.val < nZ)) ∪
          (Finset.univ.filter (fun k => ¬ k.val < nZ)) := by
        rw [Finset.filter_union_filter_neg_eq]
      have hdisj : Disjoint
          ((Finset.univ : Finset (Fin (generatorsListPackaged L).length)).filter (fun k => k.val < nZ))
          (Finset.univ.filter (fun k => ¬ k.val < nZ)) :=
        Finset.disjoint_filter_filter_neg _ _ _
      rw [hpartition, Finset.sum_union hdisj]
      -- The "left" sum (Z-block) is 0 in X-half.
      have hZ_zero : ∑ k ∈ (Finset.univ : Finset (Fin (generatorsListPackaged L).length)).filter
          (fun k => k.val < nZ),
          f k * NQubitPauliGroupElement.checkMatrix (generatorsListPackaged L) k
            (Fin.castAdd (numQubits L) (Stabilizer.Lattice.edgeToQubitIdx L e)) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        rw [Finset.mem_filter] at hk
        have hk_lt : k.val < nZ := hk.2
        have hp_eq := get_packaged_Z L ⟨k.val, hk_lt⟩ k.isLt
        set p := (coordsTrimmed L).get ⟨k.val, hk_lt⟩ with hp_def
        unfold NQubitPauliGroupElement.checkMatrix
        rw [show k = ⟨k.val, k.isLt⟩ from rfl, hp_eq]
        rw [toSymplectic_ZType_X_zero (vertexStab L p.1 p.2) (vertexStab_is_ZType L p.1 p.2)]
        ring
      rw [hZ_zero, zero_add]
      apply Finset.sum_bij (fun (k : Fin (generatorsListPackaged L).length)
        (hk : k ∈ (Finset.univ : Finset (Fin (generatorsListPackaged L).length)).filter
          (fun k => ¬ k.val < nZ)) =>
        (⟨k.val - nZ, by
          have hk_ge : nZ ≤ k.val := Nat.le_of_not_lt (Finset.mem_filter.mp hk).2
          have := k.isLt
          omega⟩ : Fin nZ))
      · intros; exact Finset.mem_univ _
      · intros a ha b hb hab
        have ha_ge : nZ ≤ a.val := Nat.le_of_not_lt (Finset.mem_filter.mp ha).2
        have hb_ge : nZ ≤ b.val := Nat.le_of_not_lt (Finset.mem_filter.mp hb).2
        have h_val : a.val - nZ = b.val - nZ := Fin.mk.inj_iff.mp hab
        apply Fin.ext
        omega
      · intros b _
        refine ⟨⟨nZ + b.val, by have := b.isLt; have := hlen; omega⟩, ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have := b.isLt
          simp only [not_lt]
          exact Nat.le_add_right _ _
        · apply Fin.ext
          simp
      · intros a ha
        have ha_ge : nZ ≤ a.val := Nat.le_of_not_lt (Finset.mem_filter.mp ha).2
        have h_fin_eq : (⟨nZ + (a.val - nZ), by have := a.isLt; omega⟩ :
            Fin (generatorsListPackaged L).length) = a := by
          apply Fin.ext
          show nZ + (a.val - nZ) = a.val
          omega
        rw [h_fin_eq]
    rw [hsum_split] at h_col
    have h_eq : ∀ k : Fin (coordsTrimmed L).length,
        NQubitPauliGroupElement.checkMatrix (generatorsListPackaged L)
          ⟨nZ + k.val, by have := k.isLt; omega⟩
          (Fin.castAdd (numQubits L) (Stabilizer.Lattice.edgeToQubitIdx L e)) =
        Stabilizer.Lattice.toricBoundary2 (L := L)
          (Stabilizer.Lattice.singleFace (L := L) ((coordsTrimmed L).get k)) e := by
      intro k
      have hge : nZ ≤ nZ + k.val := Nat.le_add_right _ _
      have hsub : nZ + k.val - nZ < nZ := by
        rw [Nat.add_sub_cancel_left]; exact k.isLt
      have hp_eq := get_packaged_X L (nZ + k.val)
        (by have := k.isLt; omega) hge hsub
      unfold NQubitPauliGroupElement.checkMatrix
      rw [hp_eq, toSymplectic_faceStab_X_eq, qubitToEdgeIdx_edgeToQubitIdx]
      -- Align indices: nZ + k.val - nZ = k.val.
      have hidx_eq : (⟨nZ + k.val - nZ, hsub⟩ : Fin nZ) = k := by
        apply Fin.ext
        simp [Nat.add_sub_cancel_left]
      have hcoord_eq : (coordsTrimmed L)[nZ + k.val - nZ]'hsub = (coordsTrimmed L).get k := by
        rw [List.get_eq_getElem]
        congr 1
        omega
      rw [hcoord_eq]
    have h_col' : ∑ k : Fin (coordsTrimmed L).length, cX k *
        Stabilizer.Lattice.toricBoundary2 (L := L)
          (Stabilizer.Lattice.singleFace (L := L) ((coordsTrimmed L).get k)) e = 0 := by
      rw [← h_col]
      apply Finset.sum_congr rfl
      intro k _
      rw [h_eq]
    rw [map_sum]
    rw [Finset.sum_apply]
    convert h_col' using 1
    apply Finset.sum_congr rfl
    intro k _
    rw [LinearMap.map_smul]
    show cX k • Stabilizer.Lattice.toricBoundary2 (L := L)
        (Stabilizer.Lattice.singleFace (L := L) ((coordsTrimmed L).get k)) e =
      cX k * Stabilizer.Lattice.toricBoundary2 (L := L)
        (Stabilizer.Lattice.singleFace (L := L) ((coordsTrimmed L).get k)) e
    rw [smul_eq_mul]
  have hX_zero : ∀ i, cX i = 0 := trimmed_combo_singleFace_eq_zero L cX h_chain_X
  -- Combine: f = 0.
  by_cases h : j.val < (coordsTrimmed L).length
  · -- Z-block index
    have hzj := hZ_zero ⟨j.val, h⟩
    show f j = 0
    have hj_eq : (⟨j.val, j.isLt⟩ : Fin (generatorsListPackaged L).length) = j := Fin.ext rfl
    rw [← hj_eq]
    exact hzj
  · -- X-block index
    push_neg at h
    have hlen : (generatorsListPackaged L).length =
        (coordsTrimmed L).length + (coordsTrimmed L).length := by
      unfold generatorsListPackaged
      rw [List.length_append, generatorsListZTrimmed_length, generatorsListXTrimmed_length]
    have hjlt : j.val - (coordsTrimmed L).length < (coordsTrimmed L).length := by
      have := j.isLt; omega
    have hxj := hX_zero ⟨j.val - (coordsTrimmed L).length, hjlt⟩
    show f j = 0
    have hj_eq : (⟨(coordsTrimmed L).length + (j.val - (coordsTrimmed L).length),
        by have := j.isLt; omega⟩ : Fin (generatorsListPackaged L).length) = j := by
      apply Fin.ext
      show (coordsTrimmed L).length + (j.val - (coordsTrimmed L).length) = j.val
      omega
    rw [← hj_eq]
    exact hxj

/-- The trimmed generator list is an independent generating set. -/
private theorem generators_independent_packaged (L : ℕ) [Fact (2 ≤ L)] :
    StabilizerGroup.GeneratorsIndependent (numQubits L) (generatorsListPackaged L) :=
  StabilizerGroup.GeneratorsIndependent_of_rowsLinearIndependent (numQubits L)
    (generatorsListPackaged L) (rowsLinearIndependent_generatorsListPackaged L)

-- ---------------------------------------------------------------------------
-- Phase 4: Final assembly
-- ---------------------------------------------------------------------------

/-- The toric code as a `StabilizerCode [[2L², 2]]`. -/
noncomputable def toricStabilizerCode (L : ℕ) [Fact (2 ≤ L)] :
    StabilizerCode (numQubits L) 2 where
  hk := by
    have hL : 2 ≤ L := Fact.out
    have hq : 2 ≤ numQubits L := by
      dsimp [numQubits]; nlinarith
    exact hq
  generatorsList := generatorsListPackaged L
  generators_length := by
    haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
    exact generatorsListPackaged_length L
  generators_phaseZero := by
    haveI : Fact (0 < L) := ⟨lt_of_lt_of_le (by decide : 0 < 2) Fact.out⟩
    exact allPhaseZero_generatorsListPackaged L
  generators_independent := generators_independent_packaged L
  generators_commute := generators_commute_packaged L
  closure_no_neg_identity := negIdentity_not_mem_packaged L
  logicalOps := toric_logicalOps L
  logical_commute_cross := toric_logical_commute_cross L

/-- The toric stabilizer code's subgroup matches the canonical `stabilizerGroup L`. -/
theorem toricStabilizerCode_subgroup_eq (L : ℕ) [Fact (2 ≤ L)] :
    (toricStabilizerCode L).toStabilizerGroup.toSubgroup = (stabilizerGroup L).toSubgroup := by
  show Subgroup.closure (listToSet (generatorsListPackaged L)) = _
  exact closure_packaged_eq_full L

end ToricCodeN
end StabilizerGroup
end Quantum
