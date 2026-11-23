# Exact monotone circuit sizes for three graph edge functions

Given one bit per vertex, the output is true exactly when the selected vertices contain both endpoints of an edge. The table gives the minimum number of AND and OR gates of fan-in at most two, with unrestricted wire reuse. Inputs cost zero. Each row combines an exhaustive computational lower bound with a Lean kernel-checked circuit attaining it.

| Graph | Desk step | Minimum gates | Largest excluded budget | C++ search tree nodes | Lean witness |
| --- | --- | ---: | ---: | ---: | --- |
| Cube on 8 vertices | L-meta-617 | **13** | 12 | 10,965,401 | [CubeUpper.upper](CubeUpper.lean) |
| Triangular prism | L-meta-618 | **10** | 9 | 37,729 | [PrismUpper.upper](PrismUpper.lean) |
| Five-spoke wheel on 6 vertices | L-meta-619 | **11** | 10 | 1,877,451 | [WheelUpper.upper](WheelUpper.lean) |

For example, partition the cube by parity into vertices 0, 3, 5, 6 on one side and 1, 2, 4, 7 on the other. Each vertex on the second side has three neighbors on the first. Six OR gates compute all four neighbor disjunctions by sharing the pairs (3, 5) and (6, 0). Four AND gates test the four vertices against their neighbor disjunctions. Three OR gates combine the answers. This gives the 13 gates in the cube witness.

## Reproduce the lower bounds

Run the following from this directory with Python 3.9+ and a C++17 compiler. The Python programs use the standard library.

```sh
python3 -B verify.py
c++ -std=c++17 -O3 audit.cpp -o /tmp/edge-audit
/tmp/edge-audit cube 12
/tmp/edge-audit prism 9
/tmp/edge-audit wheel 10
```

[verify.py](verify.py) checks the three compressed [certificates](certificates). Each header identifies the graph and the budget. Each row lists the number of remaining gates followed by the integer signatures of the live wires in increasing order. The checker reconstructs the initial state and checks closure under every admissible next gate, down to zero remaining gates. A reachable target or a missing required successor invalidates the certificate.

[audit.cpp](audit.cpp) independently reconstructs the labeled graphs, uses full truth tables, and searches in wire-creation order without memoization or graph-symmetry reduction. All three commands should report `UNSAT` with the node counts above.

To regenerate a certificate, or obtain explicit circuits in input/gate index notation, run the [search](search.py) directly. Each successful run evaluates its circuit on all 256 cube assignments or all 64 prism or wheel assignments.

```sh
python3 -B search.py cube 12 --certificate /tmp/cube.txt.gz
python3 -B verify.py /tmp/cube.txt.gz
python3 -B search.py cube 13
python3 -B search.py prism 10
python3 -B search.py wheel 11
```

## Why the search covers every minimum circuit

1. **Normalize the circuit.** In the project's [circuit semantics](../../lean/PEqualNP/Defs/CircuitLowerBounds.lean), missing wires read false. The [monotone model](../../lean/PEqualNP/Defs/MetaComplexityLgpMono.lean) permits empty gates (constants), unary gates (copies), and repeated operands. Propagate constants, bypass copies and repeated operands, and discard gates outside the output's dependencies. This preserves the function and can only decrease the gate count. Every vertex is essential because selecting a single neighbor changes from false to true when the vertex is added. Thus a minimum circuit starts with all vertex inputs and uses binary gates with distinct earlier operands.
2. **Test the boundary.** The minimal true assignments select an edge. The maximal false assignments select a maximal independent set. Every true assignment contains a minimal true one, and every false assignment lies below a maximal false one. A monotone output agreeing on these boundary tests computes the edge function everywhere. Encode a wire by its bits on the ordered boundary tests. AND and OR act bitwise. If a gate duplicates a live signature, redirect its uses to the earlier wire. The new output still agrees on the boundary and remains monotone, so such a gate cannot occur in a minimum circuit.
3. **Enumerate the live wires.** After each gate retain exactly those operands that will be read again. All other live wires stay available. Enumerating both gate types, every pair of distinct live wires, and the four operand-retention choices covers each minimum circuit in topological order. A state with m live wires needs at least m−1 more gates to reach its single output, since one gate can reduce the live count by at most one. This rule accounts for unrestricted fan-out.
4. **Check separation at each cut.** For each positive boundary assignment p and negative boundary assignment q, some live wire must be 1 on p and 0 on q. Otherwise the live vector at p is componentwise at most the one at q, and any remaining monotone circuit preserves that order. It could never return 1 on p and 0 on q. Both searches discard states that fail this necessary test.

These arguments give a finite computational lower bound for each labeled graph. The lower-bound checker runs outside Lean.

## Reproduce the Lean upper bounds

From the repository root, use the pinned Lean toolchain and the project's Mathlib dependencies.

```sh
cd lean
lake exe cache get
lake build PEqualNP.Defs
lake env lean ../research/monotone-edge-minima/CubeUpper.lean
lake env lean ../research/monotone-edge-minima/PrismUpper.lean
lake env lean ../research/monotone-edge-minima/WheelUpper.lean
```

Each theorem exhibits the circuit, verifies the gate operations and gate count, and checks the defining equivalence for every input using `decide +kernel`. The desk steps ask for smaller witnesses. This branch records the exact sizes as a separate research result.
