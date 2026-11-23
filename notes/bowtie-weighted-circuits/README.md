# Bowtie circuit weight

For the graph with edges 01, 02, 12, 03, 04, 34, the minimum of
$A+B+2D$ is 10 in the finite search below. Here $A$ counts AND gates.
$B$ and $D$ count OR gates true on at least two or at most one of the five
singleton inputs, respectively. The official L-meta-700 asks for a Lean
proof of the lower bound for all circuits and all covering index sets. Each covering set has cardinality at least the number of gates of its respective kind, even if the supplied sets overlap.

## Search and completeness argument

Run `python3 weighted.py 9 10`. The sample includes all six minimal positives,
all five maximal negatives, and all five singleton inputs (one also occurs
among the maximal negatives), for 15 distinct assignments. In low-bit-first vertex order the positive masks are 3, 5, 6, 9, 17, 24 and the maximal negative masks are 1, 10, 12, 18, 20. A wire is represented by one bit per sampled
assignment. For a monotone output, agreement on all minimal positives and
maximal negatives implies agreement everywhere. The singleton bits give every
gate its exact weight even when two distinct functions agree on the samples.

Propagate constants, replace unary gates and repeated operands with their
equivalent wire, and remove gates outside the output cone. An out-of-range
reference has constant value false. Replacing a duplicate sample signature
by an earlier wire preserves all subsequent sample values and gate costs.
Every input is essential: for each vertex there is a singleton at a neighbor
which becomes positive on adding that vertex. Thus all five inputs belong to
the output cone of a circuit that agrees with the target on the boundary.

Use gates in topological order, retaining each operand until its final use.
A step picks two distinct live wires and keeps either, both, or neither after
producing the result. A duplicate signature can be merged, so a minimum-weight
circuit is represented among these runs. With $k$ units of budget left there
can be at most $k+1$ live wires: a binary gate removes at most one net wire
and the final live set is the output alone. Also each positive/negative pair
must be distinguished in the required direction by some live wire, since
all possible suffix circuits are monotone in these wires. The search tests
both necessary conditions and caches the sorted live signatures and the
remaining weight.

At weight budget 9 the search exhausted 11,741 distinct states. At budget 10
it found a circuit, and a separate evaluation of each of its 32 inputs and
the singleton weights verified the witness. Two explicit circuits in
[Upper.lean](Upper.lean) have $(A,B,D)=(3,3,2)$ and $(3,7,0)$.

[Finite.lean](Finite.lean) uses a second representation, pairing each of the six
minimal positives with each maximal negative. It also stores the five singleton
bits. Lean evaluated `(run 9 start, run 10 start)` to `(false, true)` using its executable evaluator. This is a replay of the finite search.
The argument connecting every official circuit to a live-wire run is given above
in prose. The official lower bound was merged separately in [upstream PR 1329](https://github.com/brilliant-hq/pequalnp-proofs/pull/1329).

From the repository’s `lean` directory, replay with `lake env lean ../notes/bowtie-weighted-circuits/Finite.lean` and check both explicit circuits with `lake env lean ../notes/bowtie-weighted-circuits/Upper.lean`.
