# Mitten codes

Non-abelian lifted-product qLDPC codes (Bhardwaj et al., *High-rate qLDPC
processors*, arXiv:2607.28795): `LP(A, B)` with 1×2 base rows of weight-3
subsets of a non-abelian group `G` — five qubit blocks (2×2 grid + one
shared), rate 1/5, check weight 9.  The family-agnostic chain complex
(`lconv`/`rconv`, the L/R-commutation chain law, `mittenChainComplex`)
lives in `QEC/Stabilizer/Framework/Homological/LiftedProduct.lean`.

## `M150/` — the `[[150, 30, 10]]` instance (`G = C₅×S₃`)

| File | Contents | Status |
|---|---|---|
| `Data.lean` | **GENERATED — DO NOT HAND-EDIT.** GAP dictionary, Table XIII sets, pivot/decoder certificates (`pivX/pivZ`, `wX/wZ`), symplectic logical supports (`logXsup/logZsup`), witness supports. Regen: `qec-lab$ uv run python experiments/bb_lab/scripts/m150_gen_lean_data.py instance --out <this dir> --force` (falsify-first: every table numpy-validated before emission). | green |
| `Defs.lean` | `M150G`, indicator polynomials `m150A/m150B`, `m150Complex`, card/`numQubits` lemmas. | green |
| `StabilizerCode.lean` | M2 packaging → `m150StabilizerCode : StabilizerCode m150Complex.numQubits 30` (`m150_numQubits : … = 150`): sparse `d2term`/`cmTerm` bridges, `wX/wZ` decoder identities (full rank ⟹ no drop sets), closure equality, block-split `rowsLinearIndependent`, the 30 logical qubits. Transport bridge: `m150StabilizerCode_toSubgroup_eq`. | green |
| `Witness.lean` | M3 `d ≤ 10` half: `witChain` (weight-10 dual cycle) ∉ dual boundaries via the pairing chain and `not_mem_dualBoundaries_of_witness`. Headline: `m150_exists_weight10_nontrivial_dualCycle`. | green |
| `FloorCore.lean` | M4 generic mask/sweep layer: fueled + table popcount, `xorFold` linearity/`linear_ext`/`linear_pred`, `masksOfWt` completeness, the 4-mode `checkSplit` driver with one soundness lemma per mode, `checkJoin` + `checkJoin_sound`, `packTriple`/`pack5` extraction, parity functionals, composite-fold transfer. Fully symbolic. | green |
| `FloorData.lean` | **GENERATED — DO NOT HAND-EDIT.** M4 sweep tables, mode-assigned split lists, packed census lists (`cls*`), join row tables (`rows{X,Z}pk`), and the bridge-layer raw/inverse tables (`tRawAX`, `tCinvX*`, `tRawCZ*`, `tAinvZ`). Regen: `… m150_gen_lean_data.py m4 --out <this dir> --force`. | green |
| `FloorSweep{X,Z}.lean` | The six M4 `native_decide` compute leaves: 4 instance sweeps (all 95 even splits classify into the census) + 2 `t`-joins (every compatible classified pair is a generator row). | green |
| `FloorBridge.lean` | M4 chain↔mask bridge: canonical `maskOf`/`comask`, the `maskOf_op` transfer principle, sparse-entry block maps (`entrySum`/`blockMapped`), weight bridges (`popCntGo_maskOf`, `chainWeight_eq_sum_suppCard`). | green |
| `FloorZSide.lean` | The `ker H_X` floor `floorZ : dualBoundary c = 0 → chainWeight c ≤ 9 → c ∈ dualBoundaries`: equation transfer, per-triple parity + split coverage, mode dispatch into the sweep soundness lemmas, `t`-join, row reconstruction (`packX_inj`), `cutMap`-singleton row membership. | green |
| `FloorXSide.lean` | Mirror `floorX : ∂₁ c = 0 → chainWeight c ≤ 9 → c ∈ boundaries` on the `ker H_Z` side (rows of `H_X` via `∂₂`-singletons). | green |
| `Distance.lean` | M5 capstones: `m150_logical_weight_ge_10` (floors through `chainWeight_lower_bound_transfers`), `m150StabilizerCode_hasCodeDistance_10`, and the bundle **`mitten150StabilizerCodeWithDistance : StabilizerCodeWithDistance 150 30 10`**. | green |

**The certification is complete**: `#print axioms` on the bundle =
`propext`, `Classical.choice`, `Quot.sound` + the `native_decide`
compiler axioms of the listed leaves — no sorries, nothing else.  It is
the library's largest bundled `[[n,k,d]]` object, its first qLDPC one,
and the first formally verified non-abelian lifted-product distance.
Ground truth cross-check: `d_X = d_Z = 10` SAT-certified two ways
(`qec-lab:experiments/bb_lab/certificates/mitten_150_30_10_{X,Z}.cert.json`).

Attempt state, plan, and the binding build-time budget ledger:
`qec-lab:pipeline/attempts/mitten_150_30_10/`.  Read qec-lab's `CLAUDE.md`
before pipeline-side work; per the budget rules, decidable facts stay
batched (few `native_decide` invocations over packed tables) and
enumeration lives offline in the emitter.
