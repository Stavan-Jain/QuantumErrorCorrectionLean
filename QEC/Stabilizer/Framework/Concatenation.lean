import QEC.Stabilizer.Framework.Concatenation.Embedding
import QEC.Stabilizer.Framework.Concatenation.Promotion
import QEC.Stabilizer.Framework.Concatenation.Constructor
import QEC.Stabilizer.Framework.Concatenation.Restriction
import QEC.Stabilizer.Framework.Concatenation.Correspondence
import QEC.Stabilizer.Framework.Concatenation.Distance
import QEC.Stabilizer.Framework.Concatenation.Independence

/-!
# Framework.Concatenation

Infrastructure for **code concatenation** (Tiers 0–1b of the CSS concatenation
plan, `qec-lab:pipeline/attempts/concat_css_general/`).

Sub-modules:
- `QEC.Stabilizer.Framework.Concatenation.Embedding` (M1) — `qIdx` / `blockOf` /
  `posOf` block indexing and `embedBlock` (place an inner operator into one
  block), with weight, support, multiplicativity, and parity-commutation lemmas.
  Depends on `Foundations` only.
- `QEC.Stabilizer.Framework.Concatenation.Promotion` (M2) — the `I ↦ I`,
  `X ↦ X̄₁`, `Z ↦ Z̄₁` promotion map (`promoteE`), the `ConcatCSSData` input
  bundle, and the concatenated generator list with its length / phase-zero /
  CSS-typing lemmas. Sits at the `Framework.Symplectic` tier (uses
  `StabilizerCode`, the CSS predicates, and `AllPhaseZero`).
- `QEC.Stabilizer.Framework.Concatenation.Constructor` (M3) — the
  `concatenate : ConcatCSSData → StabilizerCode (n₁ * n₂) k₂` constructor. All
  obligation proofs discharged; `concatenate` is `sorry`-free.
- `QEC.Stabilizer.Framework.Concatenation.Restriction` (M5, part 1) — the
  block-restriction calculus `restrictBlock b g`, weight additivity
  (`weight_eq_sum_restrictBlock`), the anticommuting-count parity bridge, and
  `restrictBlock_mem_centralizer` (every block restriction of a centralizing
  element centralizes the inner stabilizer).
- `QEC.Stabilizer.Framework.Concatenation.Correspondence` (M5, part 2) — the
  induced outer operator `inducedOuter D g` (the per-block inner logical class),
  the induced parity bridge, `inducedOuter_mem_centralizer`,
  `inducedOuter_support_eq` (a block is in the support iff its restriction is a
  nontrivial inner logical — uses M4), and the R7 coset injectivity
  (`inducedOuter_isNontrivialLogical`, fully proven).
- `QEC.Stabilizer.Framework.Concatenation.Distance` (M6) — the distance lower
  bound `weight_ge_d1_mul_d2` (every nontrivial logical has weight ≥ d₁·d₂) and
  the headline
  `concat_hasCodeDistance : HasCodeDistance (concatenate D) (d₁·d₂)` (the
  weight-d₁·d₂ witness is a hypothesis, discharged per-instance in M7).
- `QEC.Stabilizer.Framework.Concatenation.Independence` — the structural
  generator-independence lemma `rowsLinearIndependent_concat` /
  `generatorsIndependent_concat`, discharging the `GeneratorsIndependent`
  hypothesis of `concatenate` from two *small* inputs (inner generators with the
  two inner logicals, and the outer generators) instead of the
  `2^(n₁n₂−k₂)`-infeasible direct check. Engine: the `blockRestrictSymp` linear
  map plus the general `rowsLinearIndependent_append_iff`.
-/
