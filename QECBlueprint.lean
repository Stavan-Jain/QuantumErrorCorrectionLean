import Architect
import QEC

/-!
# QECBlueprint — LeanArchitect annotations for the QECLean blueprint

This module carries the blueprint annotations for the whole library. It defines
no mathematics: every command below is an `attribute [blueprint ...]`
application that attaches informal LaTeX exposition to a declaration that
already exists in `QEC`.

## Why the annotations live here rather than at each declaration

`@[blueprint]` is normally written inline on the declaration it describes, which
requires `import Architect` in every annotated file. That would make
`LeanArchitect` a hard dependency of the `QEC` library for every downstream
consumer. Applying the attribute post-hoc from a single module keeps `QEC`
dependency-free and makes the blueprint an opt-in extra `lean_lib`
(`QECBlueprint`, deliberately outside `defaultTargets`).

Nothing is lost by doing it this way. `LeanArchitect` reads the environment, so
dependency inference and the sorry-free `leanok` check work exactly as they do
for inline annotations; the extracted node is recorded against *this* module
while the emitted `lean{...}` link still points at the defining source file. The
one difference is that docstrings inside tactic proofs are not picked up, so
proof exposition is written out explicitly in `(proof := ...)` — which is what a
blueprint wants anyway.

## How the graph is built

`LeanArchitect` walks each tagged constant's type and value and stops as soon as
it reaches another tagged constant, so an edge `A → B` means "B is the nearest
blueprint ancestor of A". Choosing the node set below therefore *is* choosing
the shape of the dependency graph — no dependency is written by hand.

## Conventions used below

* Titles and statements are `plainDocComment`s, never string literals: a Lean
  string would treat a LaTeX backslash as an escape sequence.
* Every node carries an explicit LaTeX label so the blueprint prose in
  `blueprint/src/content.tex` can refer to it stably even if a Lean declaration
  is later renamed.

## Rebuilding

```
lake build QECBlueprint            -- elaborate the annotations
lake build QECBlueprint:blueprint  -- emit the LaTeX under .lake/build/blueprint
leanblueprint web && leanblueprint pdf
```

See `blueprint/README.md`. Use `#show_blueprint Some.Decl` to inspect a single
extracted node.
-/

/-! ## Chapter 1 — The Pauli group -/

attribute [blueprint "def:pauli-operator"
  (title := /-- Single-qubit Pauli operator -/)
  (statement := /-- The four single-qubit Pauli *operators* $I$, $X$, $Y$, $Z$,
    taken without a phase. This is the operator part of a Pauli group element;
    the phase is tracked separately by \cref{def:pauli-group-element}. -/)]
  Quantum.PauliOperator

attribute [blueprint "def:pauli-group-element"
  (title := /-- Single-qubit Pauli group element -/)
  (statement := /-- An element of the single-qubit Pauli group
    $\mathcal{P}_1 = \{\, i^a P : a \in \Z_4,\ P \in \{I,X,Y,Z\} \,\}$,
    represented as a pair of a phase exponent $a \in \Z_4$ and an operator $P$
    (\cref{def:pauli-operator}). Splitting the phase off from the operator is
    what makes the $n$-qubit multiplication rule computable. -/)]
  Quantum.PauliGroupElement

attribute [blueprint "def:nqubit-pauli-operator"
  (title := /-- $n$-qubit Pauli operator -/)
  (statement := /-- An $n$-qubit Pauli *operator* is a function
    $\mathrm{Fin}\,n \to \{I,X,Y,Z\}$, i.e. one single-qubit Pauli per qubit.
    Again this is the phase-free part. -/)]
  Quantum.NQubitPauliOperator

attribute [blueprint "def:nqubit-pauli-group"
  (title := /-- The $n$-qubit Pauli group -/)
  (statement := /-- An element of the $n$-qubit Pauli group $\mathcal{P}_n$ is a
    phase exponent in $\Z_4$ together with an $n$-qubit Pauli operator
    (\cref{def:nqubit-pauli-operator}), i.e. a tensor product
    $i^a\, P_1 \otimes \cdots \otimes P_n$. Every operator statement in this
    development is ultimately a statement about elements of
    $\mathcal{P}_n$. -/)]
  Quantum.NQubitPauliGroupElement

attribute [blueprint "def:pauli-to-matrix"
  (title := /-- Matrix representation -/)
  (statement := /-- The unitary matrix $i^a\, P_1 \otimes \cdots \otimes P_n$ on
    $(\C^2)^{\otimes n}$ represented by a Pauli group element. This is the
    semantic anchor of the formalization: it is what makes the syntactic
    bookkeeping over $\Z_4 \times \{I,X,Y,Z\}^n$ a statement about operators on
    a Hilbert space. -/)]
  Quantum.NQubitPauliGroupElement.toMatrix

attribute [blueprint "def:pauli-mulop"
  (title := /-- Multiplication of Pauli operators -/)
  (statement := /-- Multiplication of two phase-free $n$-qubit Pauli operators,
    returning a full group element: multiplying qubitwise produces a Pauli
    operator together with an accumulated phase in $\Z_4$, since e.g.
    $XZ = -iY$. -/)]
  Quantum.NQubitPauliGroupElement.mulOp

attribute [blueprint "thm:pauli-mul-assoc"
  (title := /-- The Pauli group is a group -/)
  (statement := /-- Multiplication on $\mathcal{P}_n$ is associative. Together
    with the unit $I^{\otimes n}$ and the inverse $g^{-1} = i^{-a}P$ this makes
    \cref{def:nqubit-pauli-group} a group. -/)
  (proof := /-- Both sides have the same operator part, since qubitwise
    multiplication on $\{I,X,Y,Z\}$ is associative. For the phase part the
    accumulated exponents agree in $\Z_4$; this is checked qubitwise by
    exhausting the triples of single-qubit operators. -/)]
  Quantum.NQubitPauliGroupElement.mul_assoc

attribute [blueprint "def:pauli-support"
  (title := /-- Support -/)
  (statement := /-- The support of $g \in \mathcal{P}_n$ is the set of qubits on
    which its operator part is not $I$. -/)]
  Quantum.NQubitPauliGroupElement.support

attribute [blueprint "def:pauli-weight"
  (title := /-- Weight -/)
  (statement := /-- The weight $\wt(g)$ of a Pauli group element is the
    cardinality of its support (\cref{def:pauli-support}) — the number of qubits
    it acts on nontrivially. Code distance is a statement about weights. -/)]
  Quantum.NQubitPauliGroupElement.weight

attribute [blueprint "def:anticommutes-at"
  (title := /-- Local anticommutation -/)
  (statement := /-- Two $n$-qubit Pauli operators *anticommute at qubit $i$* if
    their $i$-th single-qubit operators are distinct and neither is $I$. This is
    the local test whose global parity governs commutation. -/)]
  Quantum.NQubitPauliGroupElement.anticommutesAt

attribute [blueprint "thm:commutes-iff-even"
  (title := /-- Commutation is a parity condition -/)
  (statement := /-- Two elements of $\mathcal{P}_n$ commute if and only if the
    number of qubits at which they anticommute (\cref{def:anticommutes-at}) is
    even. -/)
  (proof := /-- Each qubit contributes a factor $\pm 1$ when the two operators
    are swapped: $+1$ where they commute locally, $-1$ where they anticommute.
    The global sign is the product, hence $(-1)^k$ where $k$ is the number of
    anticommuting positions, and the two elements commute exactly when $k$ is
    even. -/)]
  Quantum.NQubitPauliGroupElement.commutes_iff_even_anticommutes

attribute [blueprint "def:anticommute"
  (title := /-- Anticommutation -/)
  (statement := /-- $p$ and $q$ *anticommute* when $pq = -qp$. Anticommutation
    with a stabilizer generator is the syndrome signal that detects an
    error. -/)]
  Quantum.NQubitPauliGroupElement.Anticommute

attribute [blueprint "thm:commute-or-anticommute"
  (title := /-- Dichotomy -/)
  (statement := /-- Any two elements of $\mathcal{P}_n$ either commute or
    anticommute — there is no third case. -/)
  (proof := /-- By \cref{thm:commutes-iff-even} the sign picked up on swapping is
    $(-1)^k$ for $k$ the number of locally anticommuting qubits, and this is
    either $+1$ or $-1$. -/)]
  Quantum.NQubitPauliGroupElement.commute_or_anticommute

/-! ## Chapter 2 — The binary symplectic representation -/

attribute [blueprint "def:to-symplectic"
  (title := /-- Symplectic vector of a Pauli operator -/)
  (statement := /-- The linear-algebra shadow of a Pauli operator: an $n$-qubit
    Pauli operator is sent to a vector in $\F_2^{2n}$, recording in its first
    $n$ coordinates which qubits carry an $X$ component and in its last $n$
    which carry a $Z$ component (so $Y$ contributes to both). Products of Paulis
    become sums of vectors, which is what turns questions about the group
    $\mathcal{P}_n$ into linear algebra over $\F_2$. -/)]
  Quantum.NQubitPauliOperator.toSymplectic

attribute [blueprint "thm:to-symplectic-injective"
  (title := /-- The symplectic representation is faithful -/)
  (statement := /-- \Cref{def:to-symplectic} is injective: a Pauli operator is
    determined by its symplectic vector. Phases are of course not recorded. -/)
  (proof := /-- The pair of bits at position $i$ determines the $i$-th
    single-qubit operator, since the four Paulis $I, X, Z, Y$ are sent to the
    four distinct pairs $(0,0)$, $(1,0)$, $(0,1)$, $(1,1)$. -/)]
  Quantum.NQubitPauliOperator.toSymplectic_injective

attribute [blueprint "def:symplectic-inner"
  (title := /-- Symplectic inner product -/)
  (statement := /-- For $u = (u_X \mid u_Z)$ and $v = (v_X \mid v_Z)$ in
    $\F_2^{2n}$, the symplectic form
    $\langle u, v \rangle = u_X \cdot v_Z + u_Z \cdot v_X \in \F_2$. -/)]
  Quantum.NQubitPauliOperator.symplecticInner

attribute [blueprint "thm:commutes-iff-symplectic"
  (title := /-- Commutation is symplectic orthogonality -/)
  (statement := /-- Two elements of $\mathcal{P}_n$ commute if and only if their
    symplectic vectors are orthogonal under \cref{def:symplectic-inner}. This is
    the bridge that lets the whole theory be done with linear algebra over
    $\F_2$: an abelian subgroup becomes a self-orthogonal subspace. -/)
  (proof := /-- By \cref{thm:commutes-iff-even} commutation is the parity of the
    number of locally anticommuting qubits. Qubit $i$ contributes $1$ to
    $\langle u, v \rangle$ exactly when the two single-qubit operators there are
    distinct and neither is $I$, so the symplectic product computes precisely
    that parity. -/)]
  Quantum.NQubitPauliOperator.commutes_iff_symplectic_inner_zero

attribute [blueprint "def:check-matrix"
  (title := /-- Check matrix -/)
  (statement := /-- The check matrix of a list of $\mathcal{P}_n$ elements: the
    matrix over $\F_2$ whose rows are the symplectic vectors
    (\cref{def:to-symplectic}) of the listed generators. For a CSS code it is
    block diagonal, carrying the two classical parity-check matrices $H_X$ and
    $H_Z$ on the diagonal. -/)]
  Quantum.NQubitPauliGroupElement.checkMatrix

attribute [blueprint "def:rows-linear-independent"
  (title := /-- Independent generators -/)
  (statement := /-- The rows of the check matrix (\cref{def:check-matrix}) are
    linearly independent over $\F_2$. This is the computable criterion used to
    discharge the independence obligation of \cref{def:stabilizer-code}. -/)]
  Quantum.NQubitPauliGroupElement.rowsLinearIndependent

/-! ## Chapter 3 — Stabilizer groups and the codespace -/

attribute [blueprint "def:is-stabilized-by"
  (title := /-- Stabilized state -/)
  (statement := /-- A state $\psi$ is stabilized by $g \in \mathcal{P}_n$ when
    $g\psi = \psi$, i.e. $\psi$ is a $+1$ eigenvector of the unitary
    \cref{def:pauli-to-matrix}. -/)]
  Quantum.StabilizerGroup.IsStabilizedBy

attribute [blueprint "def:stabilizer-group"
  (title := /-- Stabilizer group -/)
  (statement := /-- A *stabilizer group* is an abelian subgroup
    $\mathcal{S} \le \mathcal{P}_n$ that does not contain $-I$. The two
    conditions are exactly what is needed for the common $+1$ eigenspace to be
    nonzero: commutativity makes the eigenspace projectors compatible, and
    excluding $-I$ rules out the contradiction $\psi = -\psi$. -/)]
  Quantum.StabilizerGroup

attribute [blueprint "thm:neg-identity-not-mem"
  (title := /-- The stabilizer omits $-I$ -/)
  (statement := /-- $-I \notin \mathcal{S}$ for any stabilizer group
    $\mathcal{S}$. -/)
  (proof := /-- Immediate from the defining field of
    \cref{def:stabilizer-group}. It is recorded separately because it is the
    obligation that concrete codes must discharge by hand, and it is the step
    that fails for a would-be "stabilizer group" generated by anticommuting
    operators. -/)]
  Quantum.StabilizerGroup.neg_identity_not_mem

attribute [blueprint "def:codespace"
  (title := /-- Codespace -/)
  (statement := /-- The codespace of $\mathcal{S}$ is the set of states
    stabilized by every element of $\mathcal{S}$ — the simultaneous $+1$
    eigenspace. Logical information is stored here. -/)]
  Quantum.StabilizerGroup.IsInCodespace

attribute [blueprint "def:stabilizer-sum"
  (title := /-- Stabilizer sum -/)
  (statement := /-- The operator $\sum_{g \in \mathcal{S}} g$, which is
    $|\mathcal{S}|$ times the orthogonal projector onto the codespace. Summing
    over the group is the standard route to showing the codespace is
    nonzero. -/)]
  Quantum.StabilizerGroup.stabilizerSum

attribute [blueprint "thm:codespace-nonempty"
  (title := /-- The codespace is nonempty -/)
  (statement := /-- Every stabilizer group has a state in its codespace. A
    stabilizer code is therefore never vacuous. -/)
  (proof := /-- The stabilizer sum \cref{def:stabilizer-sum} has trace
    $2^n \neq 0$: the identity contributes $2^n$ and every other element of
    $\mathcal{S}$ is a non-identity Pauli, hence traceless. A nonzero operator
    has a nonzero column, and rescaling that column by $|\mathcal{S}|$ gives a
    state fixed by every $g \in \mathcal{S}$, because $g$ permutes the summands
    of \cref{def:stabilizer-sum}. -/)]
  Quantum.StabilizerGroup.exists_codespace_state

attribute [blueprint "def:centralizer"
  (title := /-- Centralizer -/)
  (statement := /-- The centralizer $\mathcal{C}(\mathcal{S})$ of a stabilizer
    group inside $\mathcal{P}_n$: the Pauli operators commuting with every
    element of $\mathcal{S}$. These are exactly the operators that preserve the
    codespace, so they are the candidates for logical operators. -/)]
  Quantum.StabilizerGroup.centralizer

attribute [blueprint "thm:normalizer-eq-centralizer"
  (title := /-- Normalizer equals centralizer -/)
  (statement := /-- For a stabilizer group, the Pauli normalizer and the
    centralizer coincide. This is special to the Pauli group and is the reason
    the literature uses the two words interchangeably here. -/)
  (proof := /-- One inclusion is general. Conversely, if $g$ normalizes
    $\mathcal{S}$ then for $s \in \mathcal{S}$ we have
    $gsg^{-1} \in \mathcal{S}$, and by \cref{thm:commute-or-anticommute} that
    conjugate is $\pm s$. The value $-s$ is impossible: it would put
    $-I = (-s)s^{-1}$ in $\mathcal{S}$, contradicting
    \cref{thm:neg-identity-not-mem}. So $gsg^{-1} = s$. -/)]
  Quantum.StabilizerGroup.pauliNormalizer_eq_centralizer

attribute [blueprint "thm:stabilizer-le-centralizer"
  (title := /-- The stabilizer sits inside its centralizer -/)
  (statement := /-- $\mathcal{S} \le \mathcal{C}(\mathcal{S})$. -/)
  (proof := /-- Restatement of commutativity of \cref{def:stabilizer-group}. The
    quotient $\mathcal{C}(\mathcal{S})/\mathcal{S}$ is what carries the logical
    operators. -/)]
  Quantum.StabilizerGroup.stabilizer_le_centralizer

/-! ## Chapter 4 — Logical operators, codes, and distance -/

attribute [blueprint "def:pauli-logical"
  (title := /-- Pauli logical operator -/)
  (statement := /-- A Pauli operator is *logical* when it lies in the
    centralizer \cref{def:centralizer}, i.e. it commutes with every stabilizer
    and therefore maps the codespace to itself. -/)]
  Quantum.StabilizerGroup.IsPauliLogicalOperator

attribute [blueprint "thm:logical-iff-generators"
  (title := /-- Checking logicality on generators -/)
  (statement := /-- It suffices to test commutation against a generating set:
    $g$ is logical iff it commutes with every generator of $\mathcal{S}$. -/)
  (proof := /-- Commuting with $a$ and $b$ implies commuting with $ab$, so the
    set of elements commuting with $g$ is a subgroup; if it contains the
    generators it contains their closure. This is what makes logicality a finite
    check for every concrete code in \cref{chap:codes}. -/)]
  Quantum.StabilizerGroup.isPauliLogicalOperator_iff_commutes_generators

attribute [blueprint "def:nontrivial-logical"
  (title := /-- Nontrivial logical operator -/)
  (statement := /-- A *nontrivial* logical operator is one that acts on the
    encoded information rather than fixing it. The predicate has three
    conditions: $g$ is in the centralizer, $g \notin \mathcal{S}$, and no
    element of $\mathcal{S}$ has the same operator part as $g$.

    The third condition is easy to overlook and is what makes the CSS bridge
    arguments work: without it, $g$ could differ from a stabilizer only by a
    phase, which is not a nontrivial action on the codespace. -/)]
  Quantum.StabilizerGroup.IsNontrivialLogicalOperator

attribute [blueprint "thm:nontrivial-logical-iff"
  (title := /-- Unfolding nontriviality -/)
  (statement := /-- The three conditions of \cref{def:nontrivial-logical} spelled
    out as a conjunction, which is the form the concrete distance proofs
    consume. -/)
  (proof := /-- Definitional. -/)]
  Quantum.StabilizerGroup.IsNontrivialLogicalOperator_iff

attribute [blueprint "thm:nontrivial-logical-transfer"
  (title := /-- Transfer along equal subgroups -/)
  (statement := /-- Nontriviality only depends on the underlying subgroup, so it
    transfers between two stabilizer groups with the same carrier. -/)
  (proof := /-- All three conditions of \cref{def:nontrivial-logical} are stated
    in terms of the subgroup alone. This lemma is the glue that lets a distance
    theorem proved against a hand-built stabilizer group be reused for the
    packaged \cref{def:stabilizer-code}, whose generator list is trimmed. -/)]
  Quantum.StabilizerGroup.IsNontrivialLogicalOperator_of_toSubgroup_eq

attribute [blueprint "def:logical-qubit-ops"
  (title := /-- Logical qubit operators -/)
  (statement := /-- A bundled pair of logical $\overline{X}$ and $\overline{Z}$
    operators for each of the $k$ encoded qubits, packaged with the proofs that
    they are logical, are not stabilizers, and anticommute in the right
    pattern. -/)]
  Quantum.StabilizerGroup.LogicalQubitOps

attribute [blueprint "def:generators-independent"
  (title := /-- Independence of generators -/)
  (statement := /-- A generator list is independent when no generator lies in
    the group generated by the others, so that $|\mathcal{S}| = 2^{n-k}$ for a
    list of length $n - k$. -/)]
  Quantum.StabilizerGroup.GeneratorsIndependent

attribute [blueprint "thm:independent-of-check-matrix"
  (title := /-- Independence from the check matrix -/)
  (statement := /-- If the rows of the check matrix are linearly independent
    over $\F_2$ (\cref{def:rows-linear-independent}) then the generators are
    independent in the sense of \cref{def:generators-independent}. -/)
  (proof := /-- A relation among the generators pushes forward, under the
    homomorphism \cref{def:to-symplectic}, to a linear relation among the rows
    of the check matrix. Linear independence of the rows therefore forces the
    relation to be trivial. This converts a group-theoretic side condition into
    a rank computation over $\F_2$. -/)]
  Quantum.StabilizerGroup.GeneratorsIndependent_of_rowsLinearIndependent

attribute [blueprint "def:stabilizer-code"
  (title := /-- Stabilizer code -/)
  (statement := /-- An $[[n,k]]$ stabilizer code: a list of $n-k$ independent,
    pairwise commuting generators avoiding $-I$ --- and nothing else. The code
    *is* its stabilizer group; a choice of logical operators is derived data,
    bundled separately by \cref{def:stabilizer-code-with-logicals}. The type
    carries $n$ and $k$, so instantiating it *is* the theorem that a given
    family of operators encodes $k$ qubits into $n$. -/)]
  Quantum.StabilizerGroup.StabilizerCode

attribute [blueprint "def:stabilizer-code-with-logicals"
  (title := /-- Stabilizer code with a logical basis -/)
  (statement := /-- A \cref{def:stabilizer-code} together with $k$ pairs of
    logical operators (\cref{def:logical-qubit-ops}), one per encoded qubit,
    such that the pairs of distinct qubits commute. This is what the
    constructions that genuinely need a basis consume --- logical Clifford
    actions, the encoding step of code concatenation --- while distance
    (\cref{def:has-code-distance}) lives on the bare code. -/)]
  Quantum.StabilizerGroup.StabilizerCodeWithLogicals

attribute [blueprint "def:has-code-distance"
  (title := /-- Code distance -/)
  (statement := /-- A code *has distance $d$* when every nontrivial logical
    operator (\cref{def:nontrivial-logical}) has weight at least $d$, and some
    nontrivial logical operator has weight exactly $d$. Both halves matter: the
    lower bound is the error-correction guarantee, the witness makes the value
    exact rather than merely a bound. -/)]
  Quantum.StabilizerGroup.HasCodeDistance

attribute [blueprint "thm:distance-min-weight"
  (title := /-- Distance bounds every logical -/)
  (statement := /-- If a code has distance $d$ then every nontrivial logical
    operator has weight at least $d$; equivalently, no undetectable error of
    weight below $d$ exists. -/)
  (proof := /-- The first projection of \cref{def:has-code-distance}. -/)]
  Quantum.StabilizerGroup.HasCodeDistance.min_weight

attribute [blueprint "def:code-with-distance"
  (title := /-- Stabilizer code with distance -/)
  (statement := /-- An $[[n,k,d]]$ code: a \cref{def:stabilizer-code} bundled
    with a proof of \cref{def:has-code-distance}. The headline results of this
    development are inhabitants of this type. -/)]
  Quantum.StabilizerGroup.StabilizerCodeWithDistance

/-! ## Chapter 5 — CSS structure -/

attribute [blueprint "def:x-type"
  (title := /-- $X$-type element -/)
  (statement := /-- A Pauli group element whose operator part uses only $I$ and
    $X$, with trivial phase. -/)]
  Quantum.NQubitPauliGroupElement.IsXTypeElement

attribute [blueprint "def:z-type"
  (title := /-- $Z$-type element -/)
  (statement := /-- A Pauli group element whose operator part uses only $I$ and
    $Z$, with trivial phase. A CSS code is one whose stabilizer is generated by
    elements each of which is $X$-type (\cref{def:x-type}) or $Z$-type. -/)]
  Quantum.NQubitPauliGroupElement.IsZTypeElement

attribute [blueprint "thm:css-distance-two"
  (title := /-- A distance-two closer -/)
  (statement := /-- If every weight-one Pauli anticommutes with some stabilizer
    generator, and a weight-two nontrivial logical operator exists, then the
    code has distance exactly $2$. -/)
  (proof := /-- The anticommuting witnesses exclude weight-one elements from the
    centralizer, so by \cref{def:nontrivial-logical} no nontrivial logical
    operator has weight one; weight zero is the identity, which is a
    stabilizer. The exhibited weight-two logical then makes the minimum exactly
    two by \cref{def:has-code-distance}. This single lemma discharges the
    distance obligation for the whole family of detection codes in
    \cref{chap:codes}. -/)]
  Quantum.StabilizerGroup.hasCodeDistance_two_of_anticommute_witness

attribute [blueprint "thm:css-distance-three"
  (title := /-- A distance-three closer for CSS codes -/)
  (statement := /-- Let a CSS code have $Z$-checks and $X$-checks supported on the
    rows of two classical parity-check matrices. If both matrices have
    nonzero, pairwise distinct columns --- both classical codes have distance
    at least $3$ --- and some nontrivial logical operator of weight $3$ exists,
    then the code has distance exactly $3$. -/)
  (proof := /-- A weight-one Pauli at qubit $i$ is $Z$, detected by any $X$-row
    through $i$, or carries an $X$-component, detected by any $Z$-row through
    $i$; nonzero columns supply the rows. For a weight-two Pauli on qubits
    $i \ne j$, the anticommutation with a check is the sum of the two
    single-qubit symplectic products it sees: if exactly one qubit carries an
    $X$-component a $Z$-row through it detects the pair, and if both (or
    neither, so both are $Z$) do, a $Z$-row (resp.\ $X$-row) containing exactly
    one of $i, j$ --- which exists because the columns are distinct --- sees a
    single $1$. So no Pauli of weight one or two lies in the centralizer, and
    the exhibited weight-three logical makes the minimum exactly three by
    \cref{def:has-code-distance}. -/)]
  Quantum.StabilizerGroup.hasCodeDistance_three_of_columns

/-! ## Chapter 6 — The homological framework -/

attribute [blueprint "def:homological-code"
  (title := /-- Homological code -/)
  (statement := /-- The abstract input to the CSS-from-homology machine: a
    length-three chain complex of $\F_2$ vector spaces
    $C_2 \xrightarrow{\partial_2} C_1 \xrightarrow{\partial_1} C_0$
    with $\partial_1 \partial_2 = 0$, where $C_1$ is indexed by the physical
    qubits, $C_0$ by the $Z$-checks and $C_2$ by the $X$-checks. Every
    topological code in this development is an instance. -/)]
  Quantum.Stabilizer.Homological.HomologicalCode

attribute [blueprint "thm:boundary-comp-zero"
  (title := /-- The complex condition -/)
  (statement := /-- $\partial_1(\partial_2 c) = 0$ for every $c \in C_2$. -/)
  (proof := /-- A field of \cref{def:homological-code}, restated pointwise. It
    is exactly the statement that the $X$- and $Z$-checks of the induced CSS
    code commute. -/)]
  Quantum.Stabilizer.Homological.HomologicalCode.boundary_comp_apply

attribute [blueprint "def:cycles"
  (title := /-- Cycles -/)
  (statement := /-- $Z_1 = \ker \partial_1 \le C_1$. Under
    \cref{def:chain-x-operator} these are exactly the chains whose $X$ operator
    commutes with every $Z$-check. -/)]
  Quantum.Stabilizer.Homological.HomologicalCode.cycles

attribute [blueprint "def:boundaries"
  (title := /-- Boundaries -/)
  (statement := /-- $B_1 = \operatorname{im} \partial_2 \le C_1$: the chains
    obtained from an $X$-check, i.e. the products of stabilizer
    generators. -/)]
  Quantum.Stabilizer.Homological.HomologicalCode.boundaries

attribute [blueprint "thm:boundaries-le-cycles"
  (title := /-- Boundaries are cycles -/)
  (statement := /-- $B_1 \le Z_1$. -/)
  (proof := /-- Immediate from \cref{thm:boundary-comp-zero}. -/)]
  Quantum.Stabilizer.Homological.HomologicalCode.boundaries_le_cycles

attribute [blueprint "def:H1"
  (title := /-- First homology -/)
  (statement := /-- $H_1 = Z_1 / B_1$ (\cref{def:cycles},
    \cref{def:boundaries}). The slogan of the whole framework is
    *logical operators are homology classes*: nontrivial logical operators
    correspond to nonzero classes in $H_1$, and the code distance is the minimum
    weight of a chain representing a nonzero class. -/)]
  Quantum.Stabilizer.Homological.HomologicalCode.H1

attribute [blueprint "thm:finrank-H1"
  (title := /-- Dimension of $H_1$ -/)
  (statement := /-- $\dim H_1 = \dim Z_1 - \dim B_1$, so the number of encoded
    qubits is computed by two rank calculations. -/)
  (proof := /-- Rank-nullity for the quotient of finite-dimensional spaces,
    using \cref{thm:boundaries-le-cycles} to know the quotient is
    well-formed. -/)]
  Quantum.Stabilizer.Homological.HomologicalCode.finrank_H1_eq_cycles_sub_boundaries

attribute [blueprint "def:chain-x-operator"
  (title := /-- $X$ operator of a chain -/)
  (statement := /-- The $X$-type Pauli operator supported on the qubits in a
    $1$-chain: place $X$ where the chain is $1$ and $I$ elsewhere. This is the
    dictionary between $\F_2$ linear algebra and $\mathcal{P}_n$. -/)]
  Quantum.Stabilizer.Homological.HomologicalCode.chainXOperator

attribute [blueprint "def:chain-z-operator"
  (title := /-- $Z$ operator of a chain -/)
  (statement := /-- The $Z$-type counterpart of \cref{def:chain-x-operator},
    used for the dual side of the CSS code. -/)]
  Quantum.Stabilizer.Homological.HomologicalCode.chainZOperator

attribute [blueprint "thm:chain-x-add"
  (title := /-- The chain dictionary is a homomorphism -/)
  (statement := /-- $X(c + c') = X(c) \cdot X(c')$: addition of chains over
    $\F_2$ corresponds to multiplication of $X$-type Paulis. -/)
  (proof := /-- Qubitwise. $X \cdot X = I$ matches $1 + 1 = 0$ in $\F_2$, and
    the phase stays trivial because $X$-type operators commute. -/)]
  Quantum.Stabilizer.Homological.HomologicalCode.chainXOperator_add

attribute [blueprint "thm:x-logical-iff-cycle"
  (title := /-- $X$ logicals are cycles -/)
  (statement := /-- The $X$ operator of a chain commutes with every $Z$-check if
    and only if the chain is a cycle (\cref{def:cycles}). -/)
  (proof := /-- Commutation of $X(c)$ with the $Z$-check at vertex $v$ is, by
    \cref{thm:commutes-iff-even}, the parity of the overlap between $c$ and the
    edges meeting $v$ — which is exactly the $v$-component of $\partial_1 c$.
    Requiring this for all $v$ says $\partial_1 c = 0$. -/)]
  Quantum.Stabilizer.Homological.HomologicalCode.chainXOperator_commutes_ZGenerators_iff_mem_cycles

attribute [blueprint "thm:not-both-boundary"
  (title := /-- A nontrivial logical is not doubly trivial -/)
  (statement := /-- If a Pauli operator is a nontrivial logical operator of the
    induced CSS code, then its $X$-chain and its $Z$-chain cannot both be
    boundaries. -/)
  (proof := /-- Suppose both were. Then the corresponding $X$- and $Z$-type
    operators are each products of stabilizer generators, so their product
    $g_X g_Z$ lies in $\mathcal{S}$ and has the same operator part as $g$. That
    contradicts the third clause of \cref{def:nontrivial-logical} — the clause
    whose presence is precisely what makes this argument go through. -/)]
  Quantum.Stabilizer.Homological.HomologicalCode.not_both_boundary_of_nontrivial

attribute [blueprint "thm:chain-weight-transfer"
  (title := /-- Transferring a chain-level bound to Pauli weight -/)
  (statement := /-- A lower bound on the weight of every chain representing a
    nonzero class in $H_1$ (and dually) transfers to a lower bound on the weight
    of every nontrivial logical operator. -/)
  (proof := /-- Let $g$ be a nontrivial logical. By
    \cref{thm:not-both-boundary} at least one of its two chains is a
    non-boundary cycle, and by \cref{thm:x-logical-iff-cycle} it is a cycle.
    The hypothesised chain bound applies to it, and the weight of $g$ dominates
    the weight of each of its chains since the two supports are contained in the
    support of $g$. This theorem is the reason a purely homological argument
    settles a question about Pauli operators, and it is used unchanged by both
    the toric family and the gross code. -/)]
  Quantum.Stabilizer.Homological.HomologicalCode.chainWeight_lower_bound_transfers

/-! ## Chapter 7 — The toric code -/

attribute [blueprint "def:toric-chain-complex"
  (title := /-- The toric chain complex -/)
  (statement := /-- The $L \times L$ square lattice on the torus, packaged as a
    \cref{def:homological-code}: $C_0$ is spanned by vertices, $C_1$ by the
    $2L^2$ edges (the physical qubits), $C_2$ by faces, with $\partial_2$ the
    face boundary and $\partial_1$ the edge boundary. -/)]
  Quantum.Stabilizer.Lattice.toricHomologicalCode

attribute [blueprint "def:toric-H1"
  (title := /-- Toric homology -/)
  (statement := /-- $H_1$ of \cref{def:toric-chain-complex}, i.e. the first
    homology of the torus with $\F_2$ coefficients. -/)]
  Quantum.Stabilizer.Lattice.toricH1

attribute [blueprint "thm:toric-H1-dim"
  (title := /-- The toric code encodes two qubits -/)
  (statement := /-- $\dim_{\F_2} H_1 = 2$ for every $L \ge 2$, recovering
    $H_1(T^2; \F_2) \cong \F_2^2$ and hence $k = 2$. -/)
  (proof := /-- By \cref{thm:finrank-H1} it suffices to compute
    $\dim Z_1$ and $\dim B_1$. Rank-nullity applied to $\partial_1$ gives
    $\dim Z_1 = 2L^2 - \operatorname{rank}\partial_1$, and
    $\operatorname{rank}\partial_1 = L^2 - 1$ because the only relation among
    the vertex checks is that they all multiply to the identity. Dually
    $\operatorname{rank}\partial_2 = L^2 - 1$, the kernel of $\partial_2$ being
    spanned by the all-ones face chain. Subtracting gives $2$. -/)]
  Quantum.Stabilizer.Lattice.toric_finrank_H1_eq_two

attribute [blueprint "def:wrapping-h"
  (title := /-- Horizontal wrapping number -/)
  (statement := /-- $h(c) \in \F_2$ counts, modulo two, the vertical edges of
    the chain $c$ crossing a fixed horizontal cut of the torus — the number of
    times $c$ wraps horizontally. -/)]
  Quantum.Stabilizer.Lattice.hWrap

attribute [blueprint "def:wrapping-v"
  (title := /-- Vertical wrapping number -/)
  (statement := /-- The vertical counterpart of \cref{def:wrapping-h}. -/)]
  Quantum.Stabilizer.Lattice.vWrap

attribute [blueprint "thm:wrapping-boundary-zero"
  (title := /-- Wrapping numbers vanish on boundaries -/)
  (statement := /-- Both wrapping numbers vanish on $B_1$, so they descend to
    well-defined functions on $H_1$. -/)
  (proof := /-- It is enough to check a single face, since $\partial_2$ is
    linear and the faces span $C_2$. A face has exactly two vertical edges,
    which either both cross the cut or both miss it; either way the count is
    even. -/)]
  Quantum.Stabilizer.Lattice.h_boundary_zero

attribute [blueprint "thm:wrapping-boundary-zero"
  (statement := /-- (Vertical half of the same statement.) -/)]
  Quantum.Stabilizer.Lattice.v_boundary_zero

attribute [blueprint "def:toric-phi"
  (title := /-- The wrapping map -/)
  (statement := /-- $\varphi : H_1 \to \F_2^2$, $[c] \mapsto (h(c), v(c))$,
    well defined by \cref{thm:wrapping-boundary-zero}. -/)]
  Quantum.Stabilizer.Lattice.phi

attribute [blueprint "thm:toric-phi-equiv"
  (title := /-- Wrapping numbers classify homology -/)
  (statement := /-- $\varphi$ is a linear isomorphism $H_1 \cong \F_2^2$: a
    cycle is a boundary if and only if it wraps trivially in both
    directions. -/)
  (proof := /-- Surjectivity is witnessed by the horizontal and vertical loop
    chains. Injectivity is the substantive direction: a cycle with $h = v = 0$
    is shown to be a boundary. With \cref{thm:toric-H1-dim} giving
    $\dim H_1 = 2$, a surjection onto $\F_2^2$ is automatically injective. -/)]
  Quantum.Stabilizer.Lattice.phi_equiv

attribute [blueprint "def:toric-code"
  (title := /-- The toric code as a stabilizer code -/)
  (statement := /-- The $L \times L$ toric code presented as a
    \cref{def:stabilizer-code} with $n = 2L^2$ and $k = 2$.

    The natural generating set has $2L^2$ elements, two more than the
    $n - k = 2L^2 - 2$ that \cref{def:stabilizer-code} demands, because the
    vertex checks multiply to the identity and so do the face checks. The
    packaging therefore uses a *trimmed* list, and the homological identities
    are what prove the trimmed list generates the same subgroup. -/)]
  Quantum.StabilizerGroup.ToricCodeN.toricStabilizerCode

attribute [blueprint "thm:toric-dX"
  (title := /-- $X$ distance -/)
  (statement := /-- $d_X = L$: every nontrivial $X$-type logical operator has
    weight at least $L$, and a horizontal loop achieves it. -/)
  (proof := /-- Upper bound: the horizontal loop chain is a cycle with
    $h = 1$, hence non-boundary by \cref{thm:toric-phi-equiv}, and has exactly
    $L$ edges. Lower bound: a nontrivial class has $h = 1$ or $v = 1$; say
    $h = 1$. Then the chain meets each of the $L$ disjoint horizontal cuts an
    odd number of times, so it contains at least one edge per cut, giving at
    least $L$ edges in total. -/)]
  Quantum.StabilizerGroup.ToricCodeN.toricCodeN_dX_eq_L

attribute [blueprint "thm:toric-dZ"
  (title := /-- $Z$ distance -/)
  (statement := /-- $d_Z = L$, by the same argument on the dual lattice. -/)
  (proof := /-- The dual complex of \cref{def:toric-chain-complex} is again an
    $L \times L$ torus lattice with the roles of faces and vertices exchanged,
    so the argument of \cref{thm:toric-dX} applies verbatim to the dual
    wrapping invariants. -/)]
  Quantum.StabilizerGroup.ToricCodeN.toricCodeN_dZ_eq_L

attribute [blueprint "thm:toric-distance"
  (title := /-- The toric code has distance exactly $L$ -/)
  (statement := /-- For every $L \ge 2$ the $L \times L$ toric code
    (\cref{def:toric-code}) has distance exactly $L$, so it is an
    $[[2L^2, 2, L]]$ code. -/)
  (proof := /-- For a CSS code $d = \min(d_X, d_Z)$, and both are $L$ by
    \cref{thm:toric-dX} and \cref{thm:toric-dZ}. The chain-level bounds are
    moved to Pauli weights by \cref{thm:chain-weight-transfer}, and the result
    is transported from the hand-built stabilizer group to the packaged code of
    \cref{def:toric-code} by \cref{thm:nontrivial-logical-transfer}. -/)]
  Quantum.StabilizerGroup.ToricCodeN.toricCodeN_distance_eq_L

attribute [blueprint "def:toric-code-with-distance"
  (title := /-- The toric family, packaged -/)
  (statement := /-- The $[[2L^2, 2, L]]$ toric code as an inhabitant of
    \cref{def:code-with-distance}, for every $L \ge 2$. -/)]
  Quantum.StabilizerGroup.ToricCodeN.toricStabilizerCodeWithDistance

/-! ## Chapter 8 — Bivariate-bicycle codes and the gross code -/

attribute [blueprint "def:x-double-cover"
  (title := /-- Free $\Z_2$ cover of a bivariate-bicycle complex -/)
  (statement := /-- The data exhibiting one bivariate-bicycle complex as a free
    double cover of another: a deck transformation $\sigma$ of order two acting
    freely, commuting with both boundary maps, with the base recovered as the
    quotient. The gross $[[144,12,12]]$ code covers the $[[72,12,6]]$ base
    exactly this way, and the doubling of the distance from $6$ to $12$ is what
    the cover is used to prove. -/)]
  Quantum.Stabilizer.Homological.BB.XDoubleCoverData

attribute [blueprint "def:small-cycle-data"
  (title := /-- Small-cycle certificate -/)
  (statement := /-- The finite data certifying that a bivariate-bicycle complex
    has no light cycles: an enumeration showing that every nonzero cycle of
    weight below the target floor would produce an impossible syndrome
    pattern. -/)]
  Quantum.Stabilizer.Homological.BB.SmallCycleData

attribute [blueprint "thm:small-cycle-floor"
  (title := /-- Small-cycle floor -/)
  (statement := /-- From a \cref{def:small-cycle-data} certificate, every
    nonzero cycle has weight at least six. -/)
  (proof := /-- The certificate rules out weights one through five by a finite
    case analysis on the possible supports, each case contradicting the
    syndrome constraint $\partial_1 c = 0$. The enumeration is checked in the
    kernel rather than by compiled evaluation, so the result carries no
    compiler-trust axiom. -/)]
  Quantum.Stabilizer.Homological.BB.SmallCycleData.cycle_weight_ge_6

attribute [blueprint "thm:base-distance"
  (title := /-- The $[[72,12,6]]$ base has chain distance six -/)
  (statement := /-- Every nonzero class in the homology of the base
    bivariate-bicycle complex is represented only by chains of weight at least
    six, and six is attained. -/)
  (proof := /-- The lower bound is \cref{thm:small-cycle-floor} together with
    the check that no weight-six cycle is a boundary; the witness realises the
    bound. -/)]
  Quantum.Stabilizer.Homological.BB.base_chain_distance_eq_6

attribute [blueprint "thm:gross-logical-weight"
  (title := /-- Every gross logical has weight at least six -/)
  (statement := /-- Pulled back along the cover of \cref{def:x-double-cover},
    the base floor gives a weight-six lower bound for every nontrivial logical
    operator of the gross code. -/)
  (proof := /-- Pushing a gross chain down to the base is a chain map, so it
    sends cycles to cycles and boundaries to boundaries, and it cannot increase
    weight. If the pushed-down chain is a nonzero class, \cref{thm:base-distance}
    applies directly. -/)]
  Quantum.Stabilizer.Homological.BB.gross_logical_weight_ge_6

attribute [blueprint "thm:gross-sector-dichotomy"
  (title := /-- Safe and dangerous sectors -/)
  (statement := /-- Every nontrivial gross logical operator falls into one of
    two sectors, and in each the weight is at least twelve: the *safe* sector,
    where the two sheets of the cover contribute independently, and the
    *dangerous* sector, where they do not and a finer argument is needed. -/)
  (proof := /-- In the safe sector the class survives to each sheet separately,
    so \cref{thm:gross-logical-weight} applies twice and the weights add to at
    least $6 + 6 = 12$. The dangerous sector is where the deck transformation
    acts trivially on homology; there the hexagon and direction-pair bounds
    take over, classifying the light stabilizers and confining the remaining
    classes to Smith cosets whose floor is again twelve. -/)]
  Quantum.Stabilizer.Homological.BB.gross_pauli_distance_eq_12_of_two_sectors

attribute [blueprint "def:gross-stabilizer-code"
  (title := /-- The gross code as a stabilizer code -/)
  (statement := /-- IBM's gross code presented as a \cref{def:stabilizer-code}
    with $n = 144$ and $k = 12$. -/)]
  Quantum.Stabilizer.Homological.BB.grossStabilizerCode

attribute [blueprint "thm:gross-distance"
  (title := /-- The gross code has distance exactly twelve -/)
  (statement := /-- The gross code (\cref{def:gross-stabilizer-code}) has
    distance exactly $12$, unconditionally. -/)
  (proof := /-- The lower bound is \cref{thm:gross-sector-dichotomy}, moved from
    chains to Pauli weights by \cref{thm:chain-weight-transfer}. A weight-twelve
    logical operator is exhibited explicitly, making the distance exact rather
    than a bound. Every finite check in the argument is discharged in the
    kernel, so the theorem depends on exactly the three standard axioms. -/)]
  Quantum.Stabilizer.Homological.BB.grossStabilizerCode_hasCodeDistance_12_uncond

attribute [blueprint "def:gross-code-with-distance"
  (title := /-- The gross code, packaged -/)
  (statement := /-- The $[[144,12,12]]$ gross code as an inhabitant of
    \cref{def:code-with-distance} — the headline result of this
    development. -/)]
  Quantum.Stabilizer.Homological.BB.grossStabilizerCodeWithDistance

/-! ## Chapter 9 — Small and parametric code instances -/

attribute [blueprint "def:steane7"
  (title := /-- The Steane $[[7,1,3]]$ code -/)
  (statement := /-- The CSS code built from the classical $[7,4,3]$ Hamming
    code, with all-$X$ and all-$Z$ logical operators, packaged with its
    distance. The Hamming check matrix has as columns the seven nonzero
    vectors of $\F_2^3$, so \cref{thm:css-distance-three} applies with the same
    three rows on both sides; $X$ on qubits $\{3,5,6\}$ is the weight-three
    logical. -/)]
  Quantum.StabilizerGroup.Steane7.stabilizerCodeWithDistance

attribute [blueprint "def:shor9"
  (title := /-- The Shor $[[9,1,3]]$ code -/)
  (statement := /-- The stabilizer group of the nine-qubit Shor code, a
    repetition code of cat states — historically the first quantum
    error-correcting code. -/)]
  Quantum.StabilizerGroup.Shor9.subgroup

attribute [blueprint "def:five-qubit"
  (title := /-- The $[[5,1,3]]$ code -/)
  (statement := /-- The smallest code correcting an arbitrary single-qubit
    error, and the first non-CSS code in this development: its generators mix
    $X$ and $Z$ on the same qubit, so the CSS machinery does not apply and the
    distance argument is a direct search over weight-one and weight-two
    anti-witnesses. -/)]
  Quantum.StabilizerGroup.FiveQubit_5_1_3.stabilizerCodeWithDistance

attribute [blueprint "def:four-qubit"
  (title := /-- The $[[4,2,2]]$ code -/)
  (statement := /-- The smallest error-*detecting* code, encoding two qubits
    with distance two. Its distance is closed by
    \cref{thm:css-distance-two}. -/)]
  Quantum.StabilizerGroup.FourQubit_4_2_2.stabilizerCodeWithDistance

attribute [blueprint "def:iceberg"
  (title := /-- The iceberg family $[[2m, 2m-2, 2]]$ -/)
  (statement := /-- The parametric generalized-parity family with exactly two
    stabilizer generators, the all-$X$ and all-$Z$ operators. Distance two for
    every $m$, again via \cref{thm:css-distance-two}. -/)]
  Quantum.StabilizerGroup.Iceberg.stabilizerCodeWithDistance

attribute [blueprint "def:rotated-surface"
  (title := /-- The rotated surface code -/)
  (statement := /-- The planar $L \times L$ rotated surface code, an
    $[[L^2, 1, L]]$ family. It runs on the same homological machinery as the
    toric code but with boundary, so $\dim H_1 = 1$ rather than $2$. -/)]
  Quantum.StabilizerGroup.RotatedSurfaceCodeN.rotatedSurfaceStabilizerCodeWithDistance

attribute [blueprint "def:repetition-n"
  (title := /-- The $n$-qubit repetition code -/)
  (statement := /-- The bit-flip repetition code as a stabilizer code, with
    $Z_i Z_{i+1}$ generators. It has distance one as a *quantum* code — phase
    errors are undetectable — which is why it appears here as a degenerate
    reference point rather than as a usable code. -/)]
  Quantum.StabilizerGroup.RepetitionCodeN.stabilizerCode
