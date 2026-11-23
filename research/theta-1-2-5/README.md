# The edge function of theta(1,2,5) needs eleven gates

Two vertices are joined by three internally disjoint paths of lengths one, two and five. The graph has seven vertices and eight edges. Its edge function accepts a set exactly when it contains both endpoints of an edge.

**Exact minimum: 11 gates** in the project's fan-in-two AND/OR/NOT model. Every AND, OR and NOT costs one. Inputs are free and wires may be reused. The lower bound is computational and was checked outside Lean. [Upper.lean](Upper.lean) exhibits an eleven-gate circuit for the labeled graph in L-meta-595 and verifies all 128 inputs with Lean's kernel.

## Why the lower searches are exhaustive

Normalize a minimum circuit by replacing missing wires by false, propagating constants, bypassing copies and repeated operands, and discarding gates outside the output's dependencies. NOT takes its first argument in the project's semantics, so a nonconstant NOT uses one earlier operand. All seven inputs are essential. With only a neighbor selected, toggling the vertex changes the output. Each gate in a minimum circuit computes a nonconstant truth table different from all its still-live predecessors, or a substitution eliminates the gate. These simplifications preserve the function on all 128 assignments.

Follow this circuit in topological order, starting with every input live. On creating an AND or OR, choose two distinct live wires, add the result, and retain exactly the operands to be used again. For NOT, choose one live wire and likewise try both choices for retaining it. Other wires remain live. This enumerates each normalized minimum circuit. From a cut with m live wires at least m−1 further gates are necessary to reach the final single output. At every cut, each positive assignment and each negative assignment must have different live vectors, since a deterministic suffix cannot distinguish identical vectors. This condition applies to arbitrary placements and fan-out of NOT gates.

[full.cpp](full.cpp) assigns every wire a complete 128-bit truth table. It tracks the live vector of each assignment as a short integer, rejecting cuts when one such integer carries both output labels. It enumerates gate orders directly without graph symmetry or memoization. [replay.py](replay.py) independently uses a bit for each positive-negative pair. At each cut it tests whether the union of pairs distinguished by its live wires covers all pairs. It memoizes sorted lists of truth tables and the remaining budget. Both searches returned UNSAT at ten and SAT at eleven.

## Reproduction

Run the searches from this directory with Python 3.9+ and a C++17 compiler supporting 128-bit integers.

```sh
c++ -O3 -std=c++17 full.cpp -o /tmp/theta-size
/tmp/theta-size 10
/tmp/theta-size 11
python3 -B replay.py 10
python3 -B replay.py 11
```

| Budget | C++ search nodes | Python distinct states | Result |
| ---: | ---: | ---: | --- |
| 10 | 9,050,416 | 37,667 | UNSAT |
| 11 | 27,336,527 | 45,210 | SAT |

For the Lean check, run the following from this directory with the repository's pinned toolchain and Mathlib dependencies available.

```sh
cd ../../lean
lake build PEqualNP.Defs
lake env lean ../research/theta-1-2-5/Upper.lean
```

The desk statement requests an existential witness at budget ten. The theorem in this directory verifies the attained upper bound of eleven.
