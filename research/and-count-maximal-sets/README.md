# AND gates, maximal independent sets and induced matchings

Let a monotone circuit have free OR gates and $k$ counted AND gates in the project's `AndCountCircuit` model. Require the circuit to reject every maximal independent set of a finite simple graph and to accept every set obtained by adding one vertex to such a set. These are precisely the input tests in L-meta-632.

[CountingZeros.lean](CountingZeros.lean) proves three bounds in Lean.

| Theorem | Conclusion |
| --- | --- |
| `CountingZeros.bound` | Any family of rejected inputs whose one-vertex enlargements are all accepted has at most $2^k$ members. |
| `CountingZeros.graph_bound` | A graph satisfying the circuit tests has at most $2^k$ maximal independent sets. |
| `CountingZeros.induced_matching_bound` | Every induced matching of $t$ edges gives $t ≤ k$. |

The first theorem applies to arbitrary families of Boolean inputs. The graph theorems allow isolated vertices, empty matchings and graphs with four-cycles. The conjectured vertex-cover lower bound of L-meta-632 remains open. These results attain that bound whenever the graph has an induced matching as large as a minimum vertex cover, for example a disjoint union of nonempty stars.

## Why one bit per AND suffices

For each input set, record the Boolean value of the left side of every AND gate. Suppose two inputs $I$ and $J$ have the same record. At every gate, if any subset of their union makes that gate true, at least one of the two inputs makes it true. To prove this, propagate a true bare variable or a true earlier gate through each disjunction. At an AND the left side must be true on both inputs because its values agree. Whichever input makes the right side true therefore makes the gate true. The same implication holds for the output.

If two distinct rejected sets in the family had identical records, take a vertex in one set outside the other. Adding it to the other set would give an accepted subset of their union, contradicting the output implication. This injects the family into the Boolean functions on the $k$ gate indices.

For an induced matching, select either end of each edge and extend the selection to a maximal independent set. The selection is independent because different matching edges have no adjacent endpoints. Two selections that differ on an edge cannot extend to the same independent set. Hence there are at least $2^t$ maximal independent sets.

## Kernel verification

From the repository root with the pinned Lean toolchain and the project's Mathlib cache available, run the following.

```sh
cd lean
lake build PEqualNP.Outside.L_meta_705
lake env lean ../research/and-count-maximal-sets/CountingZeros.lean
```

The proof reuses the gate evaluation equation from [the proof of L-meta-705](../../lean/PEqualNP/Outside/L_meta_705.lean). Its mathematical content is specific to the partial input tests and allows arbitrary fan-out.
