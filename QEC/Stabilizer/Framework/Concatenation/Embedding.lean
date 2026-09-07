import QEC.Stabilizer.Foundations.PauliGroup.Commutation

/-!
# Concatenation, Tier 0: the block-embedding / reindexing calculus

This is milestone **M1** of the CSS code-concatenation plan
(`qec-lab:pipeline/attempts/concat_css_general/plan.md`).

The concatenated code lives on `n₁ * n₂` physical qubits, indexed as blocks
`(b : Fin n₂, i : Fin n₁)` via the row-major map `qIdx b i = b * n₁ + i`
(mirroring `Geometry/GridIndexing.lean`). This file provides:

* the index calculus `qIdx` / `blockOf` / `posOf` and their round-trip lemmas;
* `embedBlock`, which places an inner operator on `Fin n₁` into block `b` of
  `Fin (n₁ * n₂)` (identity elsewhere), as a **phase-0** group element
  (`ofOperator`, per the zero-phase convention — plan risk R2);
* weight behaviour (`weight_embedBlock`, block-superadditivity
  `weight_ge_of_blocks_ge`);
* commutation behaviour, derived through the **parity** characterisation only
  (`commutes_iff_even_anticommutes` / `anticommutes_iff_odd_anticommutes`),
  never a homomorphism route (plan risk R8).

All `def`s are complete; every nontrivial `lemma`/`theorem` is a tagged `sorry`
to be discharged MCP-first. There is intentionally **no** group-level
`embedBlock_mul` (plan risk R2): multiplicativity is stated at the operator
level only, by `mulOp_embedBlockOp_operators`.
-/

namespace Quantum.Concatenation

open NQubitPauliGroupElement

variable {n₁ n₂ : ℕ} [NeZero n₁]

/-! ## Index calculus: `Fin n₂ × Fin n₁ ↔ Fin (n₁ * n₂)` (row-major) -/

/-- Physical-qubit index of position `i` within block `b`: `b * n₁ + i`. -/
def qIdx (b : Fin n₂) (i : Fin n₁) : Fin (n₁ * n₂) :=
  ⟨b.val * n₁ + i.val, by
    have hb : b.val + 1 ≤ n₂ := b.isLt
    have hi : i.val < n₁ := i.isLt
    calc b.val * n₁ + i.val
        < b.val * n₁ + n₁ := by omega
      _ = (b.val + 1) * n₁ := by ring
      _ ≤ n₂ * n₁ := by gcongr
      _ = n₁ * n₂ := Nat.mul_comm n₂ n₁⟩

/-- The block a physical qubit belongs to: `q / n₁`. -/
def blockOf (q : Fin (n₁ * n₂)) : Fin n₂ :=
  ⟨q.val / n₁, Nat.div_lt_of_lt_mul q.isLt⟩

/-- The position of a physical qubit within its block: `q % n₁`. -/
def posOf (q : Fin (n₁ * n₂)) : Fin n₁ :=
  ⟨q.val % n₁, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n₁))⟩

@[simp] lemma blockOf_qIdx (b : Fin n₂) (i : Fin n₁) : blockOf (qIdx b i) = b := by
  apply Fin.ext
  simp only [blockOf, qIdx]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pos_of_ne_zero (NeZero.ne n₁)),
    Nat.div_eq_of_lt i.isLt]
  omega

@[simp] lemma posOf_qIdx (b : Fin n₂) (i : Fin n₁) : posOf (qIdx b i) = i := by
  apply Fin.ext
  simp only [posOf, qIdx]
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt i.isLt]

@[simp] lemma qIdx_blockOf_posOf (q : Fin (n₁ * n₂)) : qIdx (blockOf q) (posOf q) = q := by
  apply Fin.ext
  simp only [qIdx, blockOf, posOf]
  exact Nat.div_add_mod' q.val n₁

lemma qIdx_injective {b b' : Fin n₂} {i i' : Fin n₁} (h : qIdx b i = qIdx b' i') :
    b = b' ∧ i = i' := by
  refine ⟨?_, ?_⟩
  · have := congrArg blockOf h; simpa using this
  · have := congrArg posOf h; simpa using this

/-! ## Block embedding -/

/-- Operator-level embedding: place `op` into block `b`, identity on other
blocks. -/
def embedBlockOp (b : Fin n₂) (op : NQubitPauliOperator n₁) :
    NQubitPauliOperator (n₁ * n₂) :=
  fun q => if blockOf q = b then op (posOf q) else PauliOperator.I

/-- Group-element embedding (phase 0, per the zero-phase convention). -/
def embedBlock (b : Fin n₂) (g : NQubitPauliGroupElement n₁) :
    NQubitPauliGroupElement (n₁ * n₂) :=
  ofOperator (embedBlockOp b g.operators)

@[simp] lemma embedBlock_phasePower (b : Fin n₂) (g : NQubitPauliGroupElement n₁) :
    (embedBlock b g).phasePower = 0 := rfl

@[simp] lemma embedBlock_operators (b : Fin n₂) (g : NQubitPauliGroupElement n₁) :
    (embedBlock b g).operators = embedBlockOp b g.operators := rfl

@[simp] lemma embedBlockOp_qIdx (b : Fin n₂) (op : NQubitPauliOperator n₁) (i : Fin n₁) :
    embedBlockOp b op (qIdx b i) = op i := by
  simp [embedBlockOp]

lemma embedBlockOp_qIdx_ne {b b' : Fin n₂} (h : b ≠ b') (op : NQubitPauliOperator n₁)
    (i : Fin n₁) : embedBlockOp b op (qIdx b' i) = PauliOperator.I := by
  simp only [embedBlockOp, blockOf_qIdx]
  exact if_neg (Ne.symm h)

@[simp] lemma embedBlock_one (b : Fin n₂) :
    embedBlock b (1 : NQubitPauliGroupElement n₁) = 1 := by
  simp only [embedBlock, one_def]
  congr 1
  funext q
  simp [embedBlockOp, NQubitPauliOperator.identity]

/-! ## Multiplicativity (operator level only — NO group-level `embedBlock_mul`,
R2) -/

/-- Embedding respects operator multiplication *within a block* (phase-free). -/
lemma mulOp_embedBlockOp_operators (b : Fin n₂) (g h : NQubitPauliOperator n₁) :
    (embedBlockOp b g *ₚ embedBlockOp b h).operators
      = embedBlockOp b (g *ₚ h).operators := by
  funext q
  by_cases hb : blockOf q = b <;> simp [NQubitPauliGroupElement.mulOp, embedBlockOp, hb]

/-! ## Weight -/

@[simp] lemma support_embedBlock (b : Fin n₂) (g : NQubitPauliGroupElement n₁) :
    (embedBlock b g).support = g.support.image (qIdx b) := by
  ext q
  simp only [NQubitPauliGroupElement.support, embedBlock_operators,
    NQubitPauliOperator.mem_support, Finset.mem_image]
  constructor
  · intro hq
    by_cases hb : blockOf q = b
    · exact ⟨posOf q, by simpa [embedBlockOp, hb] using hq, by
        rw [← hb]; exact qIdx_blockOf_posOf q⟩
    · exact absurd hq (by simp [embedBlockOp, hb])
  · rintro ⟨i, hi, rfl⟩
    rwa [embedBlockOp_qIdx]

@[simp] lemma weight_embedBlock (b : Fin n₂) (g : NQubitPauliGroupElement n₁) :
    (embedBlock b g).weight = g.weight := by
  have hinj : Function.Injective (qIdx b : Fin n₁ → Fin (n₁ * n₂)) :=
    fun i i' h => (qIdx_injective h).2
  rw [show (embedBlock b g).weight = (embedBlock b g).support.card from rfl, support_embedBlock,
    Finset.card_image_of_injective _ hinj]
  rfl

omit [NeZero n₁] in
/-- The weight of a `Fin (n₁*n₂)` element is the sum of its per-block weights.
-/
lemma weight_eq_sum_block_weights (g : NQubitPauliGroupElement (n₁ * n₂)) :
    g.weight = ∑ b : Fin n₂, (g.support.filter (fun q => blockOf q = b)).card := by
  change g.support.card = _
  exact Finset.card_eq_sum_card_fiberwise (fun q _ => Finset.mem_univ _)

omit [NeZero n₁] in
/-- Block-superadditivity: if `d₁` qubits of the support land in each of `B`
blocks, the total weight is at least `d₁ * |B|`. The load-bearing input for the
distance bound. -/
theorem weight_ge_of_blocks_ge (d₁ : ℕ) (g : NQubitPauliGroupElement (n₁ * n₂))
    (B : Finset (Fin n₂))
    (hB : ∀ b ∈ B, d₁ ≤ (g.support.filter (fun q => blockOf q = b)).card) :
    d₁ * B.card ≤ g.weight := by
  rw [weight_eq_sum_block_weights]
  calc d₁ * B.card = ∑ _b ∈ B, d₁ := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ b ∈ B, (g.support.filter (fun q => blockOf q = b)).card := Finset.sum_le_sum hB
    _ ≤ ∑ b : Fin n₂, (g.support.filter (fun q => blockOf q = b)).card :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ B)

/-! ## Commutation (parity route only) -/

/-- `anticommutesAt` is false wherever the left operator is `I`. -/
lemma not_anticommutesAt_of_left_I {m : ℕ} (P Q : NQubitPauliOperator m) (i : Fin m)
    (hI : P i = PauliOperator.I) :
    ¬ NQubitPauliGroupElement.anticommutesAt P Q i := by
  simp only [NQubitPauliGroupElement.anticommutesAt, hI]
  cases Q i <;> simp

/-- `anticommutesAt` is false wherever the right operator is `I`. -/
lemma not_anticommutesAt_of_right_I {m : ℕ} (P Q : NQubitPauliOperator m) (i : Fin m)
    (hI : Q i = PauliOperator.I) :
    ¬ NQubitPauliGroupElement.anticommutesAt P Q i := by
  simp only [NQubitPauliGroupElement.anticommutesAt, hI]
  cases P i <;> simp

/-- Per-position behaviour of a same-block embedding: anticommutes at `q` iff
`q` lies in block `b` and the underlying operators anticommute at `posOf q`. -/
private lemma anticommutesAt_embedBlock_iff (b : Fin n₂) (g g' : NQubitPauliGroupElement n₁)
    (q : Fin (n₁ * n₂)) :
    NQubitPauliGroupElement.anticommutesAt
        (embedBlock b g).operators (embedBlock b g').operators q
      ↔ blockOf q = b ∧
        NQubitPauliGroupElement.anticommutesAt g.operators g'.operators (posOf q) := by
  by_cases hb : blockOf q = b
  · simp only [NQubitPauliGroupElement.anticommutesAt, embedBlock_operators, embedBlockOp, hb,
      if_true, true_and]
  · simp only [hb, false_and, iff_false]
    exact not_anticommutesAt_of_left_I _ _ q (by simp [embedBlock_operators, embedBlockOp, hb])

open Classical in
/-- Parity bridge for M3: the count of anticommuting positions of two embedded
operators in the **same** block equals that of the underlying pair. -/
lemma anticommutesAt_count_eq (b : Fin n₂) (g g' : NQubitPauliGroupElement n₁) :
    (Finset.univ.filter
        (NQubitPauliGroupElement.anticommutesAt
          (embedBlock b g).operators (embedBlock b g').operators)).card
      = (Finset.univ.filter
        (NQubitPauliGroupElement.anticommutesAt g.operators g'.operators)).card := by
  have hinj : Function.Injective (qIdx b : Fin n₁ → Fin (n₁ * n₂)) :=
    fun i i' h => (qIdx_injective h).2
  have heq : (Finset.univ.filter (NQubitPauliGroupElement.anticommutesAt
        (embedBlock b g).operators (embedBlock b g').operators))
      = (Finset.univ.filter (NQubitPauliGroupElement.anticommutesAt
        g.operators g'.operators)).image (qIdx b) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      anticommutesAt_embedBlock_iff]
    constructor
    · rintro ⟨hb, hac⟩
      exact ⟨posOf q, hac, by rw [← hb]; exact qIdx_blockOf_posOf q⟩
    · rintro ⟨i, hac, rfl⟩
      exact ⟨blockOf_qIdx b i, by rw [posOf_qIdx]; exact hac⟩
  rw [heq, Finset.card_image_of_injective _ hinj]

/-- Operators embedded in **different** blocks always commute (disjoint
supports). -/
theorem embedBlock_cross_commute {b b' : Fin n₂} (hbb : b ≠ b')
    (g g' : NQubitPauliGroupElement n₁) :
    embedBlock b g * embedBlock b' g' = embedBlock b' g' * embedBlock b g := by
  classical
  rw [commutes_iff_even_anticommutes]
  have hempty : (Finset.univ.filter (NQubitPauliGroupElement.anticommutesAt
      (embedBlock b g).operators (embedBlock b' g').operators)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro q _
    by_cases hb : blockOf q = b
    · refine not_anticommutesAt_of_right_I _ _ q ?_
      simp only [embedBlock_operators, embedBlockOp, hb]
      rw [if_neg hbb]
    · exact not_anticommutesAt_of_left_I _ _ q (by simp [embedBlock_operators, embedBlockOp, hb])
  rw [hempty, Finset.card_empty]
  exact ⟨0, rfl⟩

/-- Within one block, embedded operators commute iff the underlying ones do. -/
theorem embedBlock_commute_iff (b : Fin n₂) (g g' : NQubitPauliGroupElement n₁) :
    embedBlock b g * embedBlock b g' = embedBlock b g' * embedBlock b g
      ↔ g * g' = g' * g := by
  rw [commutes_iff_even_anticommutes, commutes_iff_even_anticommutes, anticommutesAt_count_eq]

/-- Within one block, embedded operators anticommute iff the underlying ones do.
-/
theorem embedBlock_anticommute_iff (b : Fin n₂) (g g' : NQubitPauliGroupElement n₁) :
    Anticommute (embedBlock b g) (embedBlock b g') ↔ Anticommute g g' := by
  rw [anticommutes_iff_odd_anticommutes, anticommutes_iff_odd_anticommutes,
    anticommutesAt_count_eq]

end Quantum.Concatenation
