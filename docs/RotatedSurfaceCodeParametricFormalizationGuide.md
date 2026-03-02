# Parametric Rotated Surface Code — Formalization Guide

This document specifies the **parametric rotated (planar) surface code** family for formalization in Lean 4, e.g. for use with Aristotle or manual implementation. The goal is a single parametric development that yields the code **[[L², 1, L]]** for each admissible `L`.

---

## 1. Code parameters

- **Parameter:** `L : ℕ` with **`L ≥ 3`** (so that the planar open-boundary code is well-defined).
- **Number of qubits:** `n = L²`. Use `Fin (L²)` or `L * L` as the qubit index type.
- **Code parameters:** **[[L², 1, L]]** — `L²` physical qubits, 1 logical qubit, distance `L`.

---

## 2. Qubit layout

- Qubits are arranged in an **L×L grid** in **row-major order**.
- **Index of qubit at row `r` and column `c`** (with `r, c : Fin L`):
  - `index r c = r * L + c` (as a natural number), represented as `Fin (L²)`.
- So:
  - Row `0`: qubits `0, 1, …, L-1`
  - Row `r`: qubits `r*L, r*L+1, …, r*L+(L-1)`
  - Column `c`: qubits `c, L+c, 2*L+c, …, (L-1)*L+c`

---

## 3. Stabilizer generators (overview)

- **Structure:** CSS, with Z-type and X-type generators on a **checkerboard** of plaquettes.
- **Bulk:** weight-4 (four-body) operators on the corners of square cells.
- **Boundaries:** weight-2 (two-body) operators on the four edges.
- **Total:** 4 Z-type generators and 4 X-type generators for **L = 3**; for general L the counts are:
  - Z generators: bulk Z plaquettes (checkerboard cells) + left boundary Z + right boundary Z.
  - X generators: bulk X plaquettes (the other checkerboard cells) + top boundary X + bottom boundary X.

The exact counts for general L are: **((L-1)² / 2) bulk Z + 2 boundary Z** and similarly for X (with the same total structure). For L=3 this gives 2+2=4 Z and 2+2=4 X.

---

## 4. Z-type generators (precise)

Use **phase power 0** and Pauli **Z** on the support, **I** elsewhere. Each generator is an `NQubitPauliGroupElement (L²)`.

### 4.1 Bulk Z plaquettes

- For the **rotated** layout, Z plaquettes sit on cells whose “cell index” has a fixed parity (e.g. top-left and bottom-right cells for L=3).
- **Cell (i, j)** with `0 ≤ i, j ≤ L-2` has **vertices** (qubit indices):
  - `i*L + j`, `i*L + (j+1)`, `(i+1)*L + j`, `(i+1)*L + (j+1)`.
- **Z bulk:** Include a Z generator on cell `(i,j)` for those `(i,j)` in the Z-checkerboard (e.g. `(i + j) % 2 = 0`).
- **L = 3:** Cells (0,0) and (1,1):
  - (0,0): qubits `{0, 1, 3, 4}` → **Z0**
  - (1,1): qubits `{4, 5, 7, 8}` → **Z1**

### 4.2 Left boundary Z

- The **left boundary Z** is on the **bottom two qubits of the left column**, i.e. column `0`, rows `L-2` and `L-1`.
- **Support:** `{(L-2)*L + 0, (L-1)*L + 0}` = `{(L-2)*L, (L-1)*L}` = `{L*(L-2), L*(L-1)}`.
- **L = 3:** `{3, 6}`.

### 4.3 Right boundary Z

- Right column (column `L-1`), **bottom two** rows: `(L-2)*L + (L-1)` and `(L-1)*L + (L-1)`.
- **Support:** `{(L-2)*L + (L-1), (L-1)*L + (L-1)}`.
- **L = 3:** `{2, 5}`.

---

## 5. X-type generators (precise)

Use **phase power 0** and Pauli **X** on the support, **I** elsewhere.

### 5.1 Bulk X plaquettes

- X plaquettes sit on the **other** checkerboard cells (e.g. `(i + j) % 2 = 1` for `0 ≤ i, j ≤ L-2`).
- Same vertex formula: `i*L+j`, `i*L+(j+1)`, `(i+1)*L+j`, `(i+1)*L+(j+1)`.
- **L = 3:** Cells (0,1) and (1,0):
  - (0,1): `{1, 2, 4, 5}` → **X0**
  - (1,0): `{3, 4, 6, 7}` → **X1**

### 5.2 Top boundary X

- Top row (row `0`): qubits `0, 1, …, L-1`. Use the **first two**: `{0, 1}`.
- **L = 3:** `{0, 1}`.

### 5.3 Bottom boundary X

- Bottom row (row `L-1`): qubits `(L-1)*L, …, (L-1)*L + (L-1)`. Use the **last two**: `{(L-1)*L + (L-2), (L-1)*L + (L-1)}`.
- **L = 3:** `{7, 8}`.

---

## 6. Logical operators

- **Logical X:** A string of **X** along one full “path” from one boundary to the opposite. Standard choice: the **middle column** (column `L/2` or appropriate index so the column runs top to bottom). So support = column `c_mid` where `c_mid = (L-1)/2` for odd L (e.g. L=3 → column 1).
  - **Support:** `{c_mid, L + c_mid, 2*L + c_mid, …, (L-1)*L + c_mid}`.
  - **L = 3:** `{1, 4, 7}`.

- **Logical Z:** A string of **Z** along the perpendicular direction: the **middle row**.
  - **Support:** `{r_mid*L, r_mid*L+1, …, r_mid*L+(L-1)}` with `r_mid = (L-1)/2` for odd L.
  - **L = 3:** `{3, 4, 5}` (row 1).

- Both must **commute** with all stabilizer generators and **anticommute** with each other (which holds for this choice).

---

## 7. Properties to prove (parametric or for each L)

1. **Typing:** Every Z-generator is `IsZTypeElement`; every X-generator is `IsXTypeElement`.
2. **Commutation:** All Z-generators commute pairwise; all X-generators commute pairwise; every Z-generator commutes with every X-generator (CSS).
3. **No −I:** `negIdentity (L²) ∉ Subgroup.closure generators` (use the CSS lemma with the Z and X generator sets).
4. **Independence:** The generator list has linearly independent rows (over ZMod 2) in the check matrix, and hence `GeneratorsIndependent (L²) generatorsList`.
5. **Phase zero:** Every generator has phase power 0.
6. **Logicals:** `logicalX` and `logicalZ` are in the centralizer of the stabilizer group and satisfy `Anticommute logicalX logicalZ`.
7. **StabilizerCode:** Construct `StabilizerCode (L²) 1` with the appropriate `StabilizerGroup` built from the generator list (e.g. `mkStabilizerFromGenerators`), with the above facts and a single logical qubit packaged via `LogicalQubitOps`.

---

## 8. Implementation notes for Lean

- **Parameter:** Use `L : ℕ` and a hypothesis `hL : L ≥ 3` where needed (or define the code only for odd `L ≥ 3` if that simplifies indexing the middle row/column).
- **Qubit index type:** `Fin (L * L)` or `Fin (L²)`; in Lean 4, `L²` can be `L * L` or a power definition.
- **Generators:** Define each bulk and boundary generator as a function of `L` (and cell or boundary index), building the support set and then the `NQubitPauliGroupElement (L²)` with phase 0 and the appropriate `NQubitPauliOperator` (e.g. identity with `.set` for each support qubit). Follow the pattern of `RepetitionCodeN.lean` (parametric in `n`) and the concrete definitions in `RotatedSurfaceCode3.lean` for L=3.
- **Reference:** The file `QEC/Stabilizer/Codes/RotatedSurfaceCode3.lean` is the **L = 3** instance; it uses left-boundary Z on `{3, 6}` and logicals on `{1,4,7}` and `{3,4,5}`. A parametric version should specialize to these for `L = 3`.

---

## 9. Summary table (L = 3)

| Item            | Support (qubits) | Note                    |
|-----------------|------------------|-------------------------|
| Z bulk 0        | {0, 1, 3, 4}     | Cell (0,0)              |
| Z bulk 1        | {4, 5, 7, 8}     | Cell (1,1)              |
| Z left boundary | {3, 6}           | Bottom two of left column |
| Z right boundary| {2, 5}           |                         |
| X bulk 0        | {1, 2, 4, 5}     | Cell (0,1)              |
| X bulk 1        | {3, 4, 6, 7}     | Cell (1,0)              |
| X top boundary  | {0, 1}           |                         |
| X bottom boundary | {7, 8}         |                         |
| Logical X       | {1, 4, 7}        | Middle column           |
| Logical Z       | {3, 4, 5}        | Middle row              |

This table is the single source of truth for L=3; a parametric formalization must agree with it when instantiated to `L = 3`.
