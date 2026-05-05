# A Topological Proof That the Surface Code Has Distance L

## From intuition to proof

If you've read an introduction to the toric code — say, [Arthur Pesah's excellent interactive post](https://arthurpesah.me/blog/2023-05-13-surface-code/) — you've probably seen the claim that the toric code on an $L \times L$ lattice has distance $L$. It's worth examining the standard justification for this claim carefully, because one of its steps is doing more work than it might seem.

## The standard argument and its gap

Recall that the *distance* of a quantum error-correcting code is the minimum weight of any non-trivial logical operator. To show the toric code has distance $L$, we need to verify two things:

1. There exists a non-trivial logical operator of weight $L$ (so $d \leq L$).
2. Every non-trivial logical operator has weight at least $L$ (so $d \geq L$).

The argument, as typically presented, has three steps:

1. **Logical operators are loops on the lattice.**
2. **There exist non-contractible loops on the lattice of length $L$, giving non-trivial logical operators of weight $L$.**
3. **No non-contractible loop on the lattice has length less than $L$, so no non-trivial logical operator has weight less than $L$.**

Steps 1 and 2 are straightforward: Step 1 follows directly from the stabilizer formalism, and Step 2 is proved by exhibiting a specific loop. Step 3 is more subtle: the claim that no non-contractible loop has length less than $L$ is geometrically intuitive but requires a careful argument. It feels obvious — of course you need at least $L$ edges to get around an $L \times L$ torus. But "wrapping all the way around" is doing a lot of informal work here. A non-contractible loop doesn't have to look like a straight horizontal line — it could zig-zag, include vertical segments, wander wildly across the lattice. Why can't some clever squiggly path wrap around the torus using fewer than $L$ edges? The geometric intuition is compelling, but it isn't a proof. The language of homology gives us the tools to make it one: it classifies loops by how they wrap around the torus, turning a geometric question into a linear algebra problem.

## What you'll need

This post assumes familiarity with the stabilizer formalism (stabilizer groups, codespace, logical operators, distance). If you need a refresher, Arthur Pesah's [series on the stabilizer formalism](https://arthurpesah.me/blog/2023-01-31-stabilizer-formalism-1/) is a great starting point. We'll also use basic linear algebra over $`\mathbb{F}_2`$ (vector spaces, kernels, rank-nullity), but no prior knowledge of algebraic topology — we build up everything we need from scratch.

## Roadmap

We proceed as follows. Sections 1--3 set up the lattice, define the chain complex, and introduce cycles, boundaries, and the first homology group $`H_1`$. Section 4 connects this formalism to the toric code, showing that non-trivial X-type logicals correspond to non-trivial elements of $`H_1`$, and introduces the dual lattice for Z-type logicals. Section 5 computes $`\dim(H_1) = 2`$ using rank-nullity. Section 6 defines the invariants $h$ and $v$ and establishes their key properties. Section 7 proves that these invariants give an isomorphism $`H_1 \cong \mathbb{F}_2^2`$. Finally, Section 8 combines everything to prove that the distance is exactly $L$.

---

## 1. The Lattice

We work with the surface code on a torus (periodic boundary conditions), sometimes called the *toric code*. The lattice is an $L \times L$ square grid, with all arithmetic on coordinates taken modulo $L$.

- **Vertices:** $(x, y)$ for $x, y \in \{0, 1, \ldots, L-1\}$. There are $L^2$ vertices.
- **Edges:** There are two types.
  - *Horizontal edges:* $H(x, y)$ connects vertex $(x, y)$ to vertex $(x+1, y)$. There are $L^2$ horizontal edges.
  - *Vertical edges:* $V(x, y)$ connects vertex $(x, y)$ to vertex $(x, y+1)$. There are $L^2$ vertical edges.
  - In total, there are $n = 2L^2$ edges.
- **Faces:** $F(x, y)$ is the unit square with corners $(x,y)$, $(x+1,y)$, $(x,y+1)$, $(x+1,y+1)$. There are $L^2$ faces. The boundary edges of $F(x,y)$ are:
  - Bottom: $H(x, y)$
  - Top: $H(x, y+1)$
  - Left: $V(x, y)$
  - Right: $V(x+1, y)$

Each edge borders exactly two faces. Specifically:
- $H(x, y)$ borders $F(x, y)$ (as its bottom) and $F(x, y-1)$ (as its top).
- $V(x, y)$ borders $F(x, y)$ (as its left) and $F(x-1, y)$ (as its right).

Each vertex is incident to exactly four edges: $H(x-1, y)$, $H(x, y)$, $V(x, y-1)$, and $V(x, y)$.

The toric code places one qubit on each of the $2L^2$ edges, and defines two types of stabilizers:

- **X-type stabilizers** (plaquette stabilizers): For each face $f$, apply $X$ to the four boundary edges of $f$.
- **Z-type stabilizers** (vertex stabilizers): For each vertex $v$, apply $Z$ to the four edges incident to $v$.

**Convention note.** This Lean project uses the same convention as this document:
face/plaquette checks are X-type and vertex/star checks are Z-type. Some other formalizations use
the dual convention (X ↔ Z), which is equivalent under a global Hadamard transform, so code
parameters and distance are unchanged. When comparing formulas across sources, swap labels
consistently if needed.

---

## 2. The Chain Complex over $`\mathbb{F}_2`$

Our goal is to reason algebraically about subsets of edges — which ones form closed loops, which ones are the perimeter of a set of faces, and how to tell the difference. To do this, we represent edge-sets (and vertex-sets, and face-sets) as vectors over $`\mathbb{F}_2`$, and the geometric notion of "taking the boundary" becomes a linear map. This lets us use linear algebra to study the topology of the torus.

The lattice has three kinds of objects, which we organize by dimension: vertices (0-dimensional), edges (1-dimensional), and faces (2-dimensional). We call these *0-cells*, *1-cells*, and *2-cells* respectively.

To reason about them algebraically, we represent subsets of each as vectors over $`\mathbb{F}_2 = \{0, 1\}`$ (arithmetic mod 2). A *$k$-chain* is a subset of $k$-cells, where addition corresponds to symmetric difference. The space of $k$-chains is:
- $`C_0 = \mathbb{F}_2^{L^2}`$: subsets of vertices.
- $`C_1 = \mathbb{F}_2^{2L^2}`$: subsets of edges.
- $`C_2 = \mathbb{F}_2^{L^2}`$: subsets of faces.

The *weight* of a 1-chain $`c \in C_1`$, denoted $|c|$, is the number of edges it contains.

**Definition (Boundary maps).** We define two linear maps:

$$\partial_2 : C_2 \to C_1$$

sends a single face $F(x,y)$ to the sum of its four boundary edges:

$$\partial_2(F(x,y)) = H(x,y) + H(x,y+1) + V(x,y) + V(x+1,y)$$

and extends linearly. For a subset of faces $`\mathcal{F} \subseteq C_2`$, we have $`\partial_2(\mathcal{F}) = \sum_{f \in \mathcal{F}} \partial_2(f)`$, where the sum is mod 2. Concretely, an edge $e$ is in $`\partial_2(\mathcal{F})`$ if and only if an odd number of faces in $\mathcal{F}$ have $e$ on their boundary. Since each edge borders exactly two faces, this simplifies to: $`e \in \partial_2(\mathcal{F})`$ if and only if exactly one of the two faces bordering $e$ is in $\mathcal{F}$.

$$\partial_1 : C_1 \to C_0$$

sends a single edge to the sum of its two endpoints:
- $`\partial_1(H(x,y)) = (x,y) + (x+1,y)`$
- $`\partial_1(V(x,y)) = (x,y) + (x,y+1)`$

and extends linearly. For a subset of edges $E$, vertex $v$ is in $`\partial_1(E)`$ if and only if an odd number of edges in $E$ are incident to $v$.

**Example.** Let's compute some concrete boundary maps on a 3×3 torus.

First, $`\partial_1`$ applied to a single edge: $`\partial_1(H(0,0)) = (0,0) + (1,0)`$. The two endpoints are the only vertices in the boundary.

Next, $`\partial_2`$ applied to a single face $F(0,0)$:

$$\partial_2(F(0,0)) = H(0,0) + H(0,1) + V(0,0) + V(1,0)$$

This is the set of four edges forming the perimeter of the face.

Now consider $`\partial_2`$ applied to two adjacent faces $F(0,0)$ and $F(1,0)$ (side by side horizontally). Their shared boundary edge is $V(1,0)$. Over $`\mathbb{F}_2`$:

$$\partial_2(F(0,0)) + \partial_2(F(1,0)) = H(0,0) + H(0,1) + V(0,0) + V(1,0) + H(1,0) + H(1,1) + V(1,0) + V(2,0)$$

The edge $V(1,0)$ appears twice and cancels, leaving six edges forming the outer perimeter of the two-face rectangle. This illustrates the general principle: shared (interior) edges always cancel, so $`\partial_2(\mathcal{F})`$ is the outer boundary of $\mathcal{F}$.

**Lemma 2.1.** $`\partial_1 \circ \partial_2 = 0`$.

*Proof.* It suffices to check on a single face $F(x,y)$:

$$\partial_1(\partial_2(F(x,y))) = \partial_1(H(x,y)) + \partial_1(H(x,y+1)) + \partial_1(V(x,y)) + \partial_1(V(x+1,y))$$

$$= [(x,y)+(x+1,y)] + [(x,y+1)+(x+1,y+1)] + [(x,y)+(x,y+1)] + [(x+1,y)+(x+1,y+1)]$$

Each of the four corner vertices $(x,y)$, $(x+1,y)$, $(x,y+1)$, $(x+1,y+1)$ appears exactly twice in this sum. Over $`\mathbb{F}_2`$, each cancels, giving $0$. $\square$

---

## 3. Cycles, Boundaries, and Homology

With the boundary maps in hand, we can now name the two kinds of edge-sets that matter for the toric code. A *cycle* is an edge-set with no dangling ends — every vertex has even degree. This includes single closed loops, disjoint unions of loops, and even the empty set. A *boundary* is the perimeter of some set of faces — a cycle that can be built by combining face boundaries. Every boundary is automatically a cycle (perimeters don't have dangling ends), but the converse fails: some cycles wrap around the torus without being the boundary of any set of faces. These non-boundary cycles are exactly the non-trivial logical operators of the code, and measuring "how many" of them there are is the purpose of the first homology group.

**Definition.**
- The space of *1-cycles* is $`Z_1 = \ker(\partial_1) \subseteq C_1`$: the set of edge-subsets such that every vertex is incident to an even number of edges in the subset.
- The space of *1-boundaries* is $`B_1 = \mathrm{im}(\partial_2) \subseteq C_1`$: the set of edge-subsets that arise as the boundary of some set of faces.

**Example.** We illustrate these definitions on a 3×3 torus.

*An edge-set that is not a cycle:* Take the single edge $H(0,0)$. The vertices $(0,0)$ and $(1,0)$ each have degree 1 in this edge-set — odd — so the cycle condition fails. This edge-set is not in $`Z_1`$.

*A cycle that is a boundary:* Take the four edges forming the perimeter of face $F(0,0)$: $\{H(0,0), H(0,1), V(0,0), V(1,0)\}$. Every vertex has degree 0 or 2 (the four corners each have degree 2), so this is a cycle. It equals $`\partial_2(F(0,0))`$, so it is also a boundary: it lies in $`B_1`$.

*A cycle that is not a boundary:* Take the horizontal loop $`c_h = \{H(0,0), H(1,0), H(2,0)\}`$, the full row of horizontal edges at $y=0$. Every vertex on row $y=0$ has degree 2, and all other vertices have degree 0, so $`c_h \in Z_1`$. But $`c_h \notin B_1`$: as we showed earlier, assuming $`c_h = \partial_2(\mathcal{F})`$ leads to a contradiction via the periodic boundary conditions. This is an example of a non-trivial element of $`H_1`$.

**Lemma 3.1.** $`B_1 \subseteq Z_1`$. That is, every boundary is a cycle.

*Proof.* This is an immediate consequence of Lemma 2.1. If $`c = \partial_2(\mathcal{F})`$ for some $`\mathcal{F} \in C_2`$, then $`\partial_1(c) = \partial_1(\partial_2(\mathcal{F})) = 0`$, so $`c \in Z_1`$. $\square$

We can also see this geometrically: $`\partial_2(\mathcal{F})`$ consists of all edges bordering exactly one face of $\mathcal{F}$. At any vertex $v$, consider the (up to four) faces meeting at $v$. Each face in $\mathcal{F}$ that meets $v$ contributes exactly 2 of its boundary edges incident to $v$. Over $`\mathbb{F}_2`$, each such face contributes an even number of incident boundary-edges in $`\partial_2(\mathcal{F})`$. The total count of edges of $`\partial_2(\mathcal{F})`$ incident to $v$ is a sum of even numbers, hence even.

**Definition (First homology group).** The *first homology group* of the torus over $`\mathbb{F}_2`$ is the quotient vector space:

$$H_1 = Z_1 / B_1$$

Two cycles $c, c'$ are *homologous* (written $c \sim c'$) if $`c + c' \in B_1`$, i.e., they differ by a boundary. Equivalently, $c$ and $c'$ represent the same element (coset) of $`H_1`$.

---

## 4. Connection to the Toric Code

We now connect the homological machinery of Sections 2--3 to the toric code defined in Section 1. The punchline: non-trivial X-type logicals correspond exactly to non-trivial elements of $`H_1`$ (cycles that aren't boundaries), and the same holds for Z-type logicals on the dual lattice. This means the distance question — "what is the minimum-weight non-trivial logical?" — becomes a question about homology: "what is the minimum-weight non-trivial cycle?"

### 4.1 X-type logicals as non-trivial cycles

An X-type Pauli operator is specified by an edge-subset $c$ (apply $X$ to edges in $c$ and $I$ elsewhere). We now show that the X-type logical operators correspond exactly to non-trivial elements of $`H_1`$.

**Claim 4.1.** An X-type operator on edge-set $c$ commutes with all Z-type stabilizers if and only if $`c \in Z_1`$.

*Proof.* Consider the vertex stabilizer at $v$, which applies $Z$ to the four edges incident to $v$. The X-type operator on $c$ applies $X$ to the edges in $c$. On each qubit (edge), the single-qubit operators are either $X$ and $Z$ (if the edge is in both $c$ and the stabilizer's support), or $X$ and $I$, or $I$ and $Z$, or $I$ and $I$. Since $X$ and $Z$ anticommute on a single qubit while all other pairs commute, the full operators commute if and only if they overlap on an **even** number of qubits. (Each anticommuting pair contributes a factor of $-1$; the total sign is $(-1)^{|c \cap \text{supp}(v)|}$.)

The overlap $|c \cap \text{supp}(v)|$ is exactly the number of edges in $c$ incident to $v$. So the X-type operator on $c$ commutes with the vertex stabilizer at $v$ if and only if $v$ has even degree in $c$. This holds for all $v$ if and only if $`c \in Z_1`$. $\square$

**Claim 4.2.** An X-type operator on edge-set $c$ is a product of plaquette stabilizers if and only if $`c \in B_1`$.

*Proof.* Each plaquette stabilizer for face $f$ is the X-type operator on $`\partial_2(f)`$ (the four boundary edges of $f$). Since the toric code is defined over $`\mathbb{F}_2`$ (applying the same Pauli twice gives the identity), a product of plaquette stabilizers for a face-set $\mathcal{F}$ is the X-type operator on $`\sum_{f \in \mathcal{F}} \partial_2(f) = \partial_2(\mathcal{F})`$. Conversely, every element of $`B_1 = \mathrm{im}(\partial_2)`$ is $`\partial_2(\mathcal{F})`$ for some $\mathcal{F}$, and the corresponding X-type operator is the product of those plaquettes. $\square$

Combining these:

- **An X-type operator on $c$ is an X-type stabilizer if and only if $`c \in B_1`$.**
- **An X-type operator on $c$ is a non-trivial X-type logical operator if and only if $`c \in Z_1 \setminus B_1`$**, i.e., $c$ represents a non-trivial element of $`H_1`$.

Since the toric code is a CSS code, we can define the *X-distance* $`d_X`$ and *Z-distance* $`d_Z`$ separately: $`d_X`$ is the minimum weight of a non-trivial X-type logical operator, and $`d_Z`$ is the minimum weight of a non-trivial Z-type logical operator. (We will show in Section 8.3 that the full distance satisfies $`d = \min(d_X, d_Z)`$.) By the correspondence above, the X-distance is:

$$d_X = \min\{|c| : c \in Z_1 \setminus B_1\}$$

i.e., the minimum weight of a non-trivial cycle (one that is not a boundary).

### 4.2 Z-type logicals and the dual lattice

By a completely analogous argument, Z-type logical operators correspond to non-trivial cycles of a *dual* chain complex. We now make this precise.

**Definition (Dual lattice).** The *dual lattice* of our $L \times L$ torus is constructed by:
- Placing a dual vertex $`f^*`$ at the center of each face $f$. There are $L^2$ dual vertices.
- For each edge $e$ of the primal lattice, placing a dual edge $`e^*`$ connecting the dual vertices corresponding to the two faces that border $e$. There are $2L^2$ dual edges (one for each primal edge).
- Each primal vertex $v$, which is surrounded by four faces, becomes a dual face $`v^*`$ bounded by the four dual edges corresponding to the primal edges incident to $v$.

The dual lattice is again an $L \times L$ square lattice on a torus: it has $L^2$ dual vertices, $2L^2$ dual edges, and $L^2$ dual faces, with the same local structure (every dual vertex has degree 4, every dual face has 4 boundary edges).

**The key correspondence.** A Z-type operator on primal edge-set $c$ applies $Z$ to each edge in $c$. It commutes with all X-type (plaquette) stabilizers if and only if, for every face $f$, the number of edges of $c$ on the boundary of $f$ is even. Under the primal-to-dual correspondence $`e \leftrightarrow e^*`$, this is exactly the condition that the dual edge-set $`c^* = \{e^* : e \in c\}`$ has even degree at every dual vertex — i.e., $`c^*`$ is a cycle in the dual lattice.

Similarly, the Z-type operator on $c$ is a product of vertex stabilizers if and only if $`c^*`$ is a boundary in the dual lattice (since each primal vertex stabilizer corresponds to the boundary of a dual face).

Therefore, $`d_Z`$ equals the minimum weight of a non-trivial cycle in the dual lattice. We will return to this in Section 8.3.

For now, we focus on proving $`d_X = L`$, which occupies Sections 5--8.2.

---

## 5. Dimension of $`H_1`$

How many independent non-contractible loops does the torus have? Geometrically, the answer is clearly 2: one wrapping horizontally and one wrapping vertically. In this section, we prove this rigorously by computing $`\dim(H_1) = 2`$. This tells us two things at once: the toric code encodes $k = 2$ logical qubits, and the homology group has exactly $2^2 = 4$ cosets to classify.

Since $`H_1 = Z_1 / B_1`$ is a quotient of finite-dimensional vector spaces and $`B_1 \subseteq Z_1`$, we have $`\dim(H_1) = \dim(Z_1) - \dim(B_1)`$. So we need to compute $`\dim(Z_1)`$ and $`\dim(B_1)`$ separately. Our main tool is the rank-nullity theorem.

### 5.1 Background: rank-nullity

**Theorem (Rank-nullity).** Let $T: V \to W$ be a linear map between finite-dimensional vector spaces. Then:

$$\dim(V) = \dim(\ker(T)) + \mathrm{rank}(T)$$

where $\ker(T) = \{v \in V : T(v) = 0\}$ is the kernel and $\mathrm{rank}(T) = \dim(\mathrm{im}(T))$ is the rank. In other words: the dimension of the domain splits into two pieces — the dimension of what $T$ kills (the kernel) and the dimension of what survives in the image.

We will also use one fact about transpose maps over $`\mathbb{F}_2`$. Recall that a linear map $T: V \to W$ between finite-dimensional $`\mathbb{F}_2`$-vector spaces can be represented by a matrix $M$ (with entries in $`\mathbb{F}_2`$). The *transpose* $T^T: W \to V$ is the linear map represented by $M^T$. The key property we need is:

**Fact.** $\mathrm{rank}(T) = \mathrm{rank}(T^T)$.

This follows because the rank of a matrix equals the rank of its transpose (over any field), since both equal the size of the largest nonsingular square submatrix.

### 5.2 Computing $`\dim(Z_1)`$

Recall that $`Z_1 = \ker(\partial_1)`$, where $`\partial_1: C_1 \to C_0`$ maps edge-sets to their "boundary" vertex-sets. By rank-nullity applied to $`\partial_1`$:

$$\dim(C_1) = \dim(\ker(\partial_1)) + \mathrm{rank}(\partial_1)$$

$$2L^2 = \dim(Z_1) + \mathrm{rank}(\partial_1)$$

So we need $`\mathrm{rank}(\partial_1)`$. Rather than computing this directly, it turns out to be easier to compute $`\mathrm{rank}(\partial_1^T)`$ (which equals $`\mathrm{rank}(\partial_1)`$ by the Fact above) and then find $`\dim(\ker(\partial_1^T))`$ using rank-nullity.

**What does $`\partial_1^T`$ do?** Since $`\partial_1: C_1 \to C_0`$ is a linear map from edge-space to vertex-space, its transpose $`\partial_1^T: C_0 \to C_1`$ is a linear map from vertex-space to edge-space. Concretely, $`\partial_1`$ is represented by a matrix $M$ whose rows are indexed by vertices and columns by edges, with $`M_{v,e} = 1`$ if vertex $v$ is an endpoint of edge $e$. The transpose $M^T$ has rows indexed by edges and columns by vertices, with $`M^T_{e,v} = 1`$ if $v$ is an endpoint of $e$.

So $`\partial_1^T`$ maps a subset of vertices $S \subseteq V$ to the set of edges that have an odd number of endpoints in $S$. Since every edge has exactly two endpoints, this means: $`\partial_1^T(S)`$ is the set of edges with exactly one endpoint in $S$. This is known as the *edge cut* (or *coboundary*) of $S$: the set of edges "crossing the boundary" between $S$ and its complement.

**Lemma 5.1.** $`\dim(\ker(\partial_1^T)) = 1`$.

*Proof.* We need to find all vertex-subsets $S$ such that $`\partial_1^T(S) = 0`$, i.e., such that no edge has exactly one endpoint in $S$. This means every edge has either both endpoints in $S$ or both endpoints outside $S$. Equivalently: for every pair of adjacent vertices $u, v$, either both are in $S$ or neither is.

Since the lattice is connected (there is a path of edges between any two vertices), this forces $S$ to be either the empty set or the set of all vertices. These are the only two elements of $`\ker(\partial_1^T)`$, so $`\dim(\ker(\partial_1^T)) = 1`$. $\square$

**Corollary 5.2.** $`\mathrm{rank}(\partial_1) = L^2 - 1`$.

*Proof.* By rank-nullity applied to $`\partial_1^T: C_0 \to C_1`$:

$$\mathrm{rank}(\partial_1^T) = \dim(C_0) - \dim(\ker(\partial_1^T)) = L^2 - 1$$

Since $`\mathrm{rank}(\partial_1) = \mathrm{rank}(\partial_1^T)`$, we have $`\mathrm{rank}(\partial_1) = L^2 - 1`$. $\square$

**Corollary 5.3.** $`\dim(Z_1) = L^2 + 1`$.

*Proof.* $`\dim(Z_1) = \dim(C_1) - \mathrm{rank}(\partial_1) = 2L^2 - (L^2 - 1) = L^2 + 1`$. $\square$

### 5.3 Computing $`\dim(B_1)`$

Recall that $`B_1 = \mathrm{im}(\partial_2)`$, where $`\partial_2: C_2 \to C_1`$ maps face-sets to their boundary edge-sets. We have $`\dim(B_1) = \mathrm{rank}(\partial_2)`$. By rank-nullity applied to $`\partial_2`$:

$$\dim(C_2) = \dim(\ker(\partial_2)) + \mathrm{rank}(\partial_2)$$

$$L^2 = \dim(\ker(\partial_2)) + \dim(B_1)$$

So we need $`\dim(\ker(\partial_2))`$.

**Lemma 5.4.** $`\dim(\ker(\partial_2)) = 1`$.

*Proof.* A face-set $\mathcal{F}$ is in $`\ker(\partial_2)`$ if and only if $`\partial_2(\mathcal{F}) = 0`$, meaning every edge borders an even number of faces in $\mathcal{F}$. Since each edge borders exactly two faces, this means: for every edge, either both of its neighboring faces are in $\mathcal{F}$, or neither is.

If $\mathcal{F} \neq \emptyset$, pick any $f \in \mathcal{F}$. Every face adjacent to $f$ (sharing an edge) must also be in $\mathcal{F}$. Since the face-adjacency graph on the torus is connected, $\mathcal{F}$ must be the set of all faces.

One can verify directly that $`\partial_2(\text{all faces}) = 0`$: each edge borders exactly two faces, both in $\mathcal{F}$, so each edge appears $2 \equiv 0 \pmod{2}$ times.

Therefore $`\ker(\partial_2) = \{\emptyset, \text{all faces}\}`$, and $`\dim(\ker(\partial_2)) = 1`$. $\square$

**Corollary 5.5.** $`\dim(B_1) = L^2 - 1`$.

*Proof.* $`\dim(B_1) = \mathrm{rank}(\partial_2) = \dim(C_2) - \dim(\ker(\partial_2)) = L^2 - 1`$. $\square$

### 5.4 The dimension of $`H_1`$

**Theorem 5.6.** $`\dim(H_1) = 2`$.

*Proof.* Since $`B_1 \subseteq Z_1`$ are both subspaces of $`C_1`$, and $`H_1 = Z_1 / B_1`$:

$$\dim(H_1) = \dim(Z_1) - \dim(B_1) = (L^2 + 1) - (L^2 - 1) = 2$$

$\square$

Since $`H_1`$ is a 2-dimensional vector space over $`\mathbb{F}_2`$, it has exactly $2^2 = 4$ elements (cosets).

---

## 6. The Invariants $h$ and $v$

We know from Theorem 5.6 that $`H_1`$ is a 2-dimensional vector space over $`\mathbb{F}_2`$, so it has exactly 4 elements (cosets). But the dimension count alone doesn't tell us how to *distinguish* these cosets — given a cycle, how can we tell which coset it belongs to?

To answer this, we need concrete invariants: quantities that we can compute from a cycle $c$ that (a) depend only on the coset of $c$ (i.e., don't change when we add a boundary), and (b) take different values on different cosets.

The idea is geometric. On the torus, a non-trivial cycle must "wrap around" in at least one direction. We can detect this wrapping by counting how many times a cycle crosses a given "slice" of the torus. Concretely, we will define two parity-valued invariants — $h(c)$ and $v(c)$ — that detect horizontal and vertical wrapping respectively. Together, they will give us a complete classification of cosets and, crucially, a tool for proving the distance lower bound.

### 6.1 Definitions

**Definition.** For a 1-chain $`c \in C_1`$ and $`x_0 \in \{0, \ldots, L-1\}`$, define:

$$h_{x_0}(c) = \bigl|\{y : H(x_0, y) \in c\}\bigr| \mod 2$$

the parity of horizontal edges of $c$ at $x$-coordinate $`x_0`$.

Similarly, for $`y_0 \in \{0, \ldots, L-1\}`$, define:

$$v_{y_0}(c) = \bigl|\{x : V(x, y_0) \in c\}\bigr| \mod 2$$

the parity of vertical edges of $c$ at $y$-coordinate $`y_0`$.

In what follows, we use the notation $[P]$ for the *Iverson bracket*: $[P] = 1$ if the statement $P$ is true, and $[P] = 0$ if it is false. For example, $`[H(x_0, y) \in c]`$ is 1 if the edge $`H(x_0, y)`$ belongs to $c$, and 0 otherwise.

**Example.** We compute $h$ and $v$ for three cycles on a 3×3 torus.

*The horizontal loop $`c_h = \{H(0,0), H(1,0), H(2,0)\}`$:* At each $x$-coordinate $`x_0 \in \{0,1,2\}`$, there is exactly one horizontal edge of $`c_h`$ — namely $`H(x_0, 0)`$. So $`h_{x_0}(c_h) = 1`$ for all $`x_0`$, giving $`h(c_h) = 1`$. Since $`c_h`$ contains no vertical edges, $`v(c_h) = 0`$.

*A squiggly homologous cycle $`c' = c_h + \partial_2(F(0,0))`$:* Adding the boundary of $F(0,0)$ to $`c_h`$ gives $c' = \{H(0,1), H(1,0), H(2,0), V(0,0), V(1,0)\}$ — a cycle with a detour around the face $F(0,0)$. Despite its different shape, $h(c') = 1$ and $v(c') = 0$: the same as $`c_h`$. This illustrates that $h$ and $v$ depend only on the homology class, not the specific representative.

*The boundary $`\partial_2(F(0,0)) = \{H(0,0), H(0,1), V(0,0), V(1,0)\}`$:* At $`x_0 = 0`$, there are two horizontal edges: $H(0,0)$ and $H(0,1)$. Two is even, so $`h_0(\partial_2(F(0,0))) = 0`$. At all other $x$-coordinates, there are no horizontal edges. So $`h(\partial_2(F(0,0))) = 0`$, and similarly $`v(\partial_2(F(0,0))) = 0`$, consistent with Lemma 6.3.

**Lemma 6.1.** The maps $`h_{x_0}, v_{y_0} : C_1 \to \mathbb{F}_2`$ are linear.

*Proof.* We show linearity of $`h_{x_0}`$; the argument for $`v_{y_0}`$ is identical. For 1-chains $`c, c' \in C_1`$, the chain $c + c'$ is their symmetric difference. A horizontal edge $`H(x_0, y)`$ is in $c + c'$ if and only if it is in exactly one of $c$ and $c'$. Therefore:

$$h_{x_0}(c + c') = \sum_{y} [H(x_0,y) \in c + c'] = \sum_{y} \bigl([H(x_0,y) \in c] + [H(x_0,y) \in c']\bigr) \pmod{2}$$

where the second equality holds because over $`\mathbb{F}_2`$, the indicator of "exactly one" equals the sum of the two indicators (since $1 \oplus 1 = 0 = 1 + 1 \pmod{2}$). This gives $`h_{x_0}(c + c') = h_{x_0}(c) + h_{x_0}(c')`$. $\square$

### 6.2 Independence of coordinate choice

**Lemma 6.2.** If $`c \in Z_1`$ (i.e., $c$ is a cycle), then $`h_{x_0}(c)`$ is the same for all $`x_0`$, and $`v_{y_0}(c)`$ is the same for all $`y_0`$.

*Proof.* We show $`h_{x_0}(c) = h_{x_0+1}(c)`$; the result for all $`x_0`$ then follows by induction.

Consider the $L$ vertices in the vertical column at $`x = x_0 + 1`$: the vertices $`(x_0+1, y)`$ for $y = 0, \ldots, L-1$. Since $c$ is a cycle, each vertex has even degree in $c$. Therefore:

$$\sum_{y=0}^{L-1} \deg_c(x_0+1, y) \equiv 0 \pmod{2}$$

The edges incident to vertex $`(x_0+1, y)`$ are:
- $`H(x_0, y)`$ — a horizontal edge at $x$-coordinate $`x_0`$
- $`H(x_0+1, y)`$ — a horizontal edge at $x$-coordinate $`x_0 + 1`$
- $`V(x_0+1, y-1)`$ — a vertical edge
- $`V(x_0+1, y)`$ — a vertical edge

Expanding the sum:

$$\sum_{y} [H(x_0,y) \in c] + \sum_{y} [H(x_0+1,y) \in c] + \sum_{y} [V(x_0+1,y-1) \in c] + \sum_{y} [V(x_0+1,y) \in c] \equiv 0$$

The third and fourth sums are both over the same set of $L$ vertical edges (the index $y-1$ runs over $\{0,\ldots,L-1\}$ as $y$ does, since indices are mod $L$). Therefore, they are equal and cancel mod 2:

$$\sum_{y} [H(x_0,y) \in c] + \sum_{y} [H(x_0+1,y) \in c] \equiv 0 \pmod{2}$$

This gives $`h_{x_0}(c) = h_{x_0+1}(c)`$.

The proof that $`v_{y_0}(c) = v_{y_0+1}(c)`$ is analogous, summing over the row of vertices at $`y = y_0 + 1`$. $\square$

Since $`h_{x_0}(c)`$ is independent of $`x_0`$ for cycles, we write simply $h(c)$. Likewise, we write $v(c)$.

### 6.3 Invariance under adding boundaries

**Lemma 6.3.** If $`b \in B_1`$ (i.e., $b$ is a boundary), then $h(b) = 0$ and $v(b) = 0$.

*Proof.* Let $`b = \partial_2(\mathcal{F})`$ for some face-set $\mathcal{F}$. We compute $`h_{x_0}(b)`$ for an arbitrary $`x_0`$.

A horizontal edge $`H(x_0, y)`$ is in $`\partial_2(\mathcal{F})`$ if and only if exactly one of the faces $`F(x_0, y)`$ and $`F(x_0, y-1)`$ is in $\mathcal{F}$. Let $`a_y = [\,F(x_0, y) \in \mathcal{F}\,] \in \{0,1\}`$. Then:

$$[H(x_0, y) \in b] = a_y \oplus a_{y-1}$$

Summing over $y$:

$$h_{x_0}(b) = \sum_{y=0}^{L-1} (a_y \oplus a_{y-1}) = \sum_{y=0}^{L-1} a_y + \sum_{y=0}^{L-1} a_{y-1} \pmod{2}$$

Since indices are mod $L$, both sums run over the same values. Their sum is $`2 \sum_y a_y \equiv 0 \pmod{2}`$.

The proof for $v(b) = 0$ is analogous. $\square$

**Corollary 6.4.** The map $`\varphi: H_1 \to \mathbb{F}_2^2`$ defined by $\varphi([c]) = (h(c), v(c))$ is well-defined.

*Proof.* If $c \sim c'$ (i.e., $c' = c + b$ for some $`b \in B_1`$), then by linearity of $h$ (Lemma 6.1), $h(c') = h(c + b) = h(c) + h(b) = h(c) + 0 = h(c)$, where the last step uses Lemma 6.3. Similarly $v(c') = v(c)$. So $\varphi$ depends only on the coset, not the representative. $\square$

**Lemma 6.5.** The map $`\varphi: H_1 \to \mathbb{F}_2^2`$ is linear.

*Proof.* $`\varphi([c_1] + [c_2]) = \varphi([c_1 + c_2]) = (h(c_1 + c_2), v(c_1 + c_2)) = (h(c_1) + h(c_2), v(c_1) + v(c_2)) = \varphi([c_1]) + \varphi([c_2])`$, where the third equality uses linearity of $h$ and $v$ (Lemma 6.1). $\square$

---

## 7. The Isomorphism $`H_1 \cong \mathbb{F}_2^2`$

We have established two things so far: $`H_1`$ is a 2-dimensional $`\mathbb{F}_2`$-vector space (Section 5), and we have a well-defined linear map $`\varphi: H_1 \to \mathbb{F}_2^2`$ that assigns to each cycle its $(h, v)$ invariants (Section 6). We now show that $\varphi$ is an isomorphism. This means the invariants $h$ and $v$ completely classify the cosets of $`H_1`$: two cycles are homologous if and only if they have the same $(h, v)$ values. This is the key fact that enables the distance proof in Section 8, because it guarantees that every non-trivial cycle has $h = 1$ or $v = 1$ (or both), and we will show that either condition forces the cycle to have weight at least $L$.

**Theorem 7.1.** The map $`\varphi: H_1 \to \mathbb{F}_2^2`$ is an isomorphism.

*Proof.* By Theorem 5.6, $`\dim(H_1) = 2 = \dim(\mathbb{F}_2^2)`$. Since $\varphi$ is linear (Lemma 6.5) and maps between spaces of the same finite dimension, it suffices to show that $\varphi$ is surjective (surjectivity + equal dimensions $\Rightarrow$ injectivity).

We exhibit a cycle in $`Z_1 \setminus B_1`$ for each of the three nonzero values in $`\mathbb{F}_2^2`$:

**Representative for $(1, 0)$:** Let $`c_h = \{H(x, 0) : x = 0, \ldots, L-1\}`$, the horizontal loop along row $y = 0$.

- *$`c_h`$ is a cycle:* At any vertex $(x, y)$, the edges of $`c_h`$ incident to it are $H(x-1, 0)$ and $H(x, 0)$ if $y = 0$, and none otherwise. In either case, the count is even (2 or 0).
- *$`h(c_h) = 1`$:* At $x$-coordinate $`x_0`$, the only horizontal edge of $`c_h`$ is $`H(x_0, 0)`$. So $`h_{x_0}(c_h) = 1`$.
- *$`v(c_h) = 0`$:* $`c_h`$ contains no vertical edges.
- *$`c_h`$ is not a boundary:* By Lemma 6.3, every boundary $b$ has $h(b) = 0$. Since $`h(c_h) = 1`$, $`c_h`$ cannot be a boundary.
- Therefore $`\varphi([c_h]) = (1, 0)`$.

**Representative for $(0, 1)$:** Let $`c_v = \{V(0, y) : y = 0, \ldots, L-1\}`$, the vertical loop along column $x = 0$. By an analogous argument, $`c_v`$ is a cycle with $`\varphi([c_v]) = (0, 1)`$, and $`c_v \notin B_1`$ since $`v(c_v) = 1`$ while $v(b) = 0$ for all boundaries $b$ (Lemma 6.3).

**Representative for $(1, 1)$:** Let $`c_{hv} = c_h + c_v`$ (symmetric difference). Since $\varphi$ is linear (Lemma 6.5), $`\varphi([c_{hv}]) = (1,0) + (0,1) = (1,1)`$, and $`c_{hv} \notin B_1`$ since $`\varphi([c_{hv}]) \neq (0,0)`$ while $\varphi$ sends all boundaries to $(0,0)$ (Lemma 6.3).

Thus $\varphi$ is surjective, and therefore an isomorphism. $\square$

---

## 8. The Distance Theorem

We now have all the tools we need. The isomorphism $`\varphi: H_1 \to \mathbb{F}_2^2`$ (Theorem 7.1) tells us that every non-trivial cycle must have $h(c) = 1$ or $v(c) = 1$ (or both). The independence result (Lemma 6.2) tells us that this parity is the same across all $L$ slices. Together, these force every non-trivial cycle to contribute at least one edge to each of $L$ disjoint sets, giving the lower bound. The upper bound is immediate from our explicit representatives.

**Theorem 8.1.** The X-distance of the toric code on an $L \times L$ lattice is $`d_X = L`$.

### 8.1 Upper bound: $`d_X \leq L`$

The horizontal loop $`c_h = \{H(x, 0) : x = 0, \ldots, L-1\}`$ is a non-trivial cycle (shown in Sections 6--7) with $`|c_h| = L`$. Therefore $`d_X \leq L`$.

### 8.2 Lower bound: $`d_X \geq L`$

Let $`c \in Z_1 \setminus B_1`$ be any non-trivial cycle. We must show $|c| \geq L$.

Since $\varphi$ is injective (Theorem 7.1) and $`c \notin B_1`$, we have $\varphi([c]) \neq (0, 0)$. Therefore at least one of $h(c) = 1$ or $v(c) = 1$ holds. We handle each case.

**Case 1: $h(c) = 1$.** Define, for each $x \in \{0, \ldots, L-1\}$, the set:

$$S_x = \{H(x, y) : y = 0, \ldots, L-1\}$$

the set of all horizontal edges at $x$-coordinate $x$. Note that these $L$ sets are pairwise disjoint: a horizontal edge $H(x,y)$ belongs to $`S_x`$ and no other $`S_{x'}`$.

Since $h(c) = 1$, the number of edges of $c$ in $`S_x`$ is odd for every $x$ (by Lemma 6.2, this parity is the same for all $x$, and it equals $h(c) = 1$). In particular, $`|c \cap S_x| \geq 1`$ for each $x$.

Since the $`S_x`$ are pairwise disjoint:

$$|c| \geq \sum_{x=0}^{L-1} |c \cap S_x| \geq L$$

**Case 2: $v(c) = 1$.** Define, for each $y \in \{0, \ldots, L-1\}$:

$$T_y = \{V(x, y) : x = 0, \ldots, L-1\}$$

By the same argument (with vertical and horizontal swapped), $`|c \cap T_y| \geq 1`$ for each $y$, and the $`T_y`$ are pairwise disjoint, giving $|c| \geq L$.

In both cases, $|c| \geq L$. $\square$

### 8.3 Z-type logicals and the full distance

The distance of the code is $`d = \min(d_X, d_Z)`$. We now justify this claim and compute $`d_Z`$.

**Claim 8.2.** For a CSS code, $`d = \min(d_X, d_Z)`$.

*Proof.* The distance is the minimum weight of any non-trivial logical operator. We show that every non-trivial logical has weight $`\geq \min(d_X, d_Z)`$, and that there exists one with weight exactly $`\min(d_X, d_Z)`$.

**Decomposition.** Any $n$-qubit Pauli operator $P$ can be written (up to a global phase $\pm 1, \pm i$) as $P = X^a Z^b$, where $`a, b \in \mathbb{F}_2^n`$ and $`X^a = X_1^{a_1} \otimes \cdots \otimes X_n^{a_n}`$ (and similarly for $Z^b$). Write $`\mathrm{supp}(a) = \{i : a_i = 1\}`$ for the *support* of $a$ — the set of qubits on which $X^a$ acts non-trivially. The weight of $P$ (the number of qubits on which $P$ acts non-trivially) is $|\mathrm{supp}(a) \cup \mathrm{supp}(b)|$, since $P$ acts as identity on qubit $i$ only when $`a_i = b_i = 0`$.

**Commutation.** In a CSS code, every stabilizer generator is either purely X-type or purely Z-type. We use two facts about Pauli commutation:

- $X^a Z^b$ commutes with an X-type operator $X^s$ if and only if $|\mathrm{supp}(b) \cap \mathrm{supp}(s)|$ is even. (The $X^a$ part always commutes with $X^s$; the $Z^b$ part anticommutes on each qubit where both act, contributing $(-1)^{|\mathrm{supp}(b) \cap \mathrm{supp}(s)|}$.)
- $X^a Z^b$ commutes with a Z-type operator $Z^t$ if and only if $|\mathrm{supp}(a) \cap \mathrm{supp}(t)|$ is even. (By the symmetric argument.)

Therefore, $P = X^a Z^b$ commutes with all stabilizers if and only if two **independent** conditions hold: $a$ commutes with all Z-type stabilizers (i.e., $`a \in Z_1`$), and $b$ commutes with all X-type stabilizers (i.e., $`b \in Z_1^*`$, where $`Z_1^*`$ denotes the space of cycles in the dual lattice). This decoupling of conditions on $a$ and $b$ is specific to CSS codes.

**Non-triviality.** In a CSS code, the stabilizer group factors as products of X-type stabilizers and Z-type stabilizers. Therefore $P = X^a Z^b$ is a stabilizer if and only if $X^a$ is a product of X-type stabilizers (i.e., $`a \in B_1`$) **and** $Z^b$ is a product of Z-type stabilizers (i.e., $`b \in B_1^*`$, where $`B_1^*`$ denotes the space of boundaries in the dual lattice).

Taking the contrapositive: $P$ is a non-trivial logical if and only if $P$ commutes with all stabilizers and at least one of the following holds: $`a \in Z_1 \setminus B_1`$ (the X-part is non-trivial), or $`b \in Z_1^* \setminus B_1^*`$ (the Z-part is non-trivial).

**Lower bound.** If $`a \in Z_1 \setminus B_1`$, then $`|a| \geq d_X`$, so $`\mathrm{wt}(P) = |\mathrm{supp}(a) \cup \mathrm{supp}(b)| \geq |a| \geq d_X`$. If $`b \in Z_1^* \setminus B_1^*`$, then $`|b| \geq d_Z`$, so $`\mathrm{wt}(P) \geq |b| \geq d_Z`$. Since at least one holds, $`\mathrm{wt}(P) \geq \min(d_X, d_Z)`$.

**Upper bound.** A minimum-weight non-trivial X-type logical has weight $`d_X`$ and is a valid non-trivial logical, so $`d \leq d_X`$. Similarly $`d \leq d_Z`$. Therefore $`d \leq \min(d_X, d_Z)`$.

Combining both bounds: $`d = \min(d_X, d_Z)`$. $\square$

As shown in Section 4.2, Z-type logical operators correspond to non-trivial cycles in the dual lattice, and the dual lattice of the $L \times L$ torus is again an $L \times L$ torus with the same combinatorial structure. Therefore the entire argument of Sections 5--8.2 applies verbatim to the dual lattice, yielding $`d_Z = L`$.

Thus:

$$d = \min(d_X, d_Z) = \min(L, L) = L$$

This also establishes that the toric code is a $[[2L^2, 2, L]]$ code:
- $n = 2L^2$ physical qubits (edges),
- $k = 2$ logical qubits (since $`\dim(H_1) = 2`$),
- $d = L$. $\quad\blacksquare$

---

## Conclusion

The proof rested on a single key idea: defining the invariants $h$ and $v$ that detect whether a cycle wraps around the torus horizontally or vertically. These invariants are well-defined on homology classes, completely classify the four cosets of $`H_1`$, and — crucially — force any non-trivial cycle to contain at least $L$ edges, because the regular structure of the square lattice guarantees $L$ disjoint "slices" that each contribute at least one edge.

The deeper lesson is that the distance of the toric code is a *topological* fact, not a combinatorial coincidence. It is controlled by the homology of the underlying manifold: the number of logical qubits comes from $`\dim(H_1)`$, and the distance comes from the minimum weight of a non-trivial homology class. This is why the proof naturally lives in the language of homology rather than, say, case analysis on paths.

This perspective generalizes far beyond the square lattice on a torus. The entire framework — qubits on $k$-cells, stabilizers from boundary maps, logical operators from non-trivial homology classes — works for any cellulation of any manifold in any dimension. The distance question becomes a question about the *systole* of the cellulation: the shortest non-trivial cycle. This is the foundation for hyperbolic codes, higher-dimensional toric codes, and the broader family of [homological codes](https://errorcorrectionzoo.org/c/higher_dimensional_surface).

That said, the specific argument we used for the lower bound — partitioning edges into $L$ disjoint slices with odd parity — exploits the regular structure of the $L \times L$ square lattice. For other manifolds or irregular cellulations, computing the distance can be significantly harder, and is in general an NP-hard problem. Even for close relatives of the toric code, modifications are needed: the planar and rotated surface codes have different boundary conditions that change the homology (from $`H_1 \cong \mathbb{F}_2^2`$ to $`H_1 \cong \mathbb{F}_2`$), and the distance argument must account for paths that terminate at boundaries rather than wrapping around.

### Further reading

- [Arthur Pesah's interactive introduction to the surface code](https://arthurpesah.me/blog/2023-05-13-surface-code/) for the broader surface code picture, including the planar and rotated variants, decoding, and thresholds.
- [Arthur Pesah's series on the stabilizer formalism](https://arthurpesah.me/blog/2023-01-31-stabilizer-formalism-1/) for the algebraic foundations underlying the toric code.
- [Alice Wang's REU paper](https://math.uchicago.edu/~may/REU2024/REUPapers/Wang,Alice.pdf) for another rigorous treatment of the toric code distance using the homological framework.
- [Nikolas Breuckmann's thesis, *Homological Quantum Codes Beyond the Toric Code*](http://www.nikobreu.website/files/PhDThesis.pdf), for a thorough treatment of homological codes on general manifolds, including hyperbolic surfaces and the connection to systolic geometry.
