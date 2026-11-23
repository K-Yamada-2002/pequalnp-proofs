# Monotone circuits for the Heawood edge function

The 14 inputs indicate a subset of vertices. The output is true when the subset contains an edge. Points are labeled 0 through 6 and lines 7 through 13, using the 21 incidences in desk step L-meta-582. Gates are AND or OR of fan-in at most two. Input wires are free and fan-out is unrestricted.

**The 26-gate desk question remains open.** The [Lean theorem HeawoodUpper.upper](HeawoodUpper.lean) exhibits a circuit with 27 gates on the posted edge list. The unrestricted computational lower bound obtained here is 22. If each path from an input to the output contains at most one AND, the minimum is exactly 27.

For a partial incidence graph, retain all edges at a nonempty subset of the seven points. Delete the other points and ignore isolated lines. The following bounds concern unrestricted circuits for that partial graph.

| Points retained | Inequivalent choices (labeled multiplicities) | Minimum gates |
| ---: | --- | --- |
| 1 | 1 (7) | 3 |
| 2 | 1 (21) | 7 |
| 3 | 2 (28 and 7) | 11 in both |
| 4 | 2 (28 and 7) | 15 in both |
| 5 | 1 (21) | 18 to 19 |
| 6 | 1 (7) | 20 to 23 |
| 7 | 1 (1) | 22 to 27 |

Each upper bound comes from one three-neighbor OR per point (two gates), one AND with that point, and an OR tree joining all the point terms. For k points this costs 4k−1 gates. For the complete graph, Lean verifies the 27-gate witness symbolically for every input. The lower bounds in this note use mathematical arguments and finite computations outside Lean. Point-line duality gives the same bounds for subsets of lines.

In particular, partitioning the seven points into groups of at most four, synthesizing each group's circuit independently and joining the group outputs by OR always costs at least 27 gates. A possible saving must involve a larger group or sharing across groups.

## The restriction to one AND per path

Remove unused gates and propagate missing inputs (false), constants, copies, and repeated operands. Since every singleton must be rejected, an input cannot reach the output through ORs alone. Every remaining AND forms the conjunction of two nonempty disjunctions of inputs and feeds the output through ORs alone. Its two sets of inputs must be disjoint, and every cross pair must be an edge. Otherwise a singleton or a nonedge pair would be accepted. Two points are incident with just one common line, so the graph has no four-cycle. At least one side of every such complete bipartite subgraph is a singleton. The AND therefore describes a star, possibly a single edge. Choose a center for each star.

Write p for the number of ANDs. Their centers cover all 21 edges. The seven disjoint incidences (0,7), (1,13), (2,8), (3,12), (4,10), (5,9), (6,11) give p ≥ 7. Fix a center c, let q be its number of stars, and let d be the number of distinct leaves in their union. The q leaf disjunctions need at least d−q OR gates in total. Indeed, connect each variable to the output disjunctions in which it occurs by its OR computation. The resulting undirected network has at most q components, and each binary OR can merge at most two components. Any useful OR combining two distinct leaf variables belongs to just one center: its pair of inputs' underlying vertices cannot have two common neighbors. OR gates denoting single variables can be bypassed. Thus the leaf-side costs sum across centers. The sum of the d values counts every edge at least once, so at least 21−p ORs precede the ANDs. At least p−1 more ORs connect the p ANDs to one output. This gives 21+p−1 ≥ 27. The Lean witness attains the bound.

## Exhaustive search on partial graphs

The [instance generator](make_instance.py) enumerates the seven-point permutations that preserve the seven incidence triples. Their induced permutations on lines preserve the whole graph. It checks the orbits of point subsets and uses only symmetries preserving the selected subset to choose representatives of the first gate. Both gate types are tested for each representative.

The [C++ search](boundary.cpp) represents a wire by its values on two families of assignments. The minimal positive assignments are edge pairs. The maximal negative assignments are maximal independent sets. Agreement with the target on this boundary implies agreement everywhere by monotonicity. A wire can be replaced by a previous wire or input that is true on at least the same positives and false on at least the same negatives. Monotonicity of the suffix proves this substitution sound, even when the two signatures differ. A signal false on every positive or true on every negative can likewise be replaced by a constant. Such redundant gates cannot occur in a minimum circuit.

At a cut, keep precisely the wires still to be used. For each next gate, take two distinct live wires and try both operations and all four possibilities for retaining its operands. Every vertex of the normalized graph is essential. To finish with one wire from m live wires takes at least m−1 more gates. In addition, for every positive assignment p and negative assignment q some live wire must be true on p and false on q. If this fails, the componentwise order of the live vectors prevents any monotone suffix from computing the target. The search memoizes rejected live-signature sets with their remaining gate budgets. The cache can be cleared without affecting correctness.

For the five-point graph, deleting any one point gives a four-point graph of minimum size 15. The search uses this fact at each cut. For each such deletion let L count processed gates simplified away by constant operands, and let Z count the currently live zero wires. At least Z further gates in the suffix can be eliminated. To see this, send one token from each zero wire along a chosen outgoing edge. A gate receiving two tokens produces zero and passes one token onward. A gate receiving one token absorbs it. Each receiving gate simplifies and absorbs just one token. The output of the restricted graph is nonconstant, so a two-token gate cannot be the output. All Z tokens are eventually absorbed at different gates. Hence a circuit with total budget b must satisfy L+Z ≤ b−15 at every cut. The projected search enforces this inequality for all five deletions. The induction starts with Z=1. A gate with a zero operand increments L, a new zero increments Z, and forgetting a zero operand decrements Z.

## Lower bound for the complete graph

[restrict.py](restrict.py) computes lower bounds recursively on induced subgraphs. The bipartite vertex cover construction above generalizes by assigning each edge to an incident cover vertex. For the forest and maximum-degree-two base cases the matching lower bounds come from the project's [forest theorem](../../lean/PEqualNP/MetaComplexity/L104.lean) and [peelable-graph theorem](../../lean/PEqualNP/MetaComplexity/L532.lean). Induced subgraphs here of degree at most two are disjoint unions of paths, isolated vertices, and cycles of length at least six. Every nonempty edge component supplies a good leaf or a run of six in the project's definition. The program also uses the partial-graph lower bounds above.

For each possible first binary gate on inputs u and v, set one or both of them to zero or one. The gate always disappears. When its output is constant its first reader also disappears. That reader is distinct from every other direct reader of u or v: a gate combining the first result with one of its operands would simplify by absorption or idempotence. When a different direct reader is necessary and its input is assigned, that gate disappears too. For an AND, u needs another reader if u still matters at v=0, equivalently if u has a neighbor other than v. For an OR, u needs another reader if it still matters at v=1, equivalently if its neighborhood is not contained in v's. Interchange u and v for the other test. If both need another reader and the vertices are not interchangeable, they need at least two distinct other readers between them. Otherwise all their uses would be symmetric in u and v.

The cofactor with an adjacent pair set to one is constant. Otherwise its function is the OR of the still-free neighbors of true vertices and the edge function on the remaining induced subgraph. If a residual edge remains, fixing each of those singleton inputs to zero saves at least one gate, since the singleton is essential and the output is not a projection. If only singleton inputs remain, their disjunction costs their count minus one for a nonempty set. Take the best lower bound among these restrictions at each first gate, then the minimum over first gates. On the full graph the minimum is 21; the first-AND cases require at least 22. This recurrence gives a lower bound and does not synthesize a circuit at that budget.

### Ruling out 21 gates

The [prefix checker](prefix.py) takes the preceding recurrence as a source of lower bounds for smaller graphs. It tries every first-gate class and then all allowed continuations to the indicated depth. At every cut it tests deletions of one vertex, two vertices, and same-side triples. Each projection has a lower bound for its surviving edge graph. Any vertices that become isolated can be set to zero.

For each projection, a live wire that is false on all surviving edge assignments may be replaced by zero: this preserves every positive boundary value and can only decrease values on negative assignments. An OR whose output agrees with one operand on all surviving edges can similarly be bypassed. Throughout the simplified prefix every wire agrees with its original on all surviving edges and can only be smaller on negatives. This invariant justifies updating the eliminated-gate and live-zero counts using just the surviving positive bits. The same suffix token argument applies after these additional simplifications. An honest prefix of a minimum circuit must respect every projection's budget. The checker also stops with a surviving prefix if the target is reached early.

For the entire graph, with a total budget of 21, only two first-gate states survive after taking symmetries into account. They are the OR of point 0 with incident line 7, or with nonincident line 9, with both operands retained. Neither admits a second gate compatible with all the projections. For a six-point block, with a total budget of 19, all prefixes close within six gates. Its seven labeled choices are equivalent. The five-point budget of 18 remains unresolved in this work.

## Reproduce

From this directory, use Python 3.10+ and a C++17 compiler. No third-party Python packages are required.

```sh
python3 -B make_instance.py --orbits
c++ -O3 -std=c++17 boundary.cpp -o /tmp/heawood-search
for points in 0 01 012 013 0123 0125; do
    budget=$((4 * ${#points} - 2))
    python3 -B make_instance.py "$points" "$budget" > /tmp/heawood.in
    /tmp/heawood-search < /tmp/heawood.in
done
python3 -B make_instance.py 01234 17 > /tmp/heawood-five.in
/tmp/heawood-search 3600 5 15 < /tmp/heawood-five.in
python3 -B restrict.py
python3 -B prefix.py
```

The optional C++ arguments are a time limit in seconds, the number of initial point inputs to project separately, and the established lower bound after one point deletion. An interrupted search prints `UNKNOWN`. Increase any of the first six budgets by one to obtain a positive control. The recorded run is in [results.txt](results.txt). The complete graph's Lean verification can be rerun from the repository root with the pinned Lean toolchain and Mathlib cache.

```sh
cd lean
lake exe cache get
lake build PEqualNP.Defs.MetaComplexityLgpMono
lake env lean ../research/heawood/HeawoodUpper.lean
```
