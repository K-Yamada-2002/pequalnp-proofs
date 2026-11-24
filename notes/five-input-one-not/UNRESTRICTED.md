# Exact circuit sizes with unrestricted negations on five inputs

Every monotone Boolean function on five labelled inputs has an optimal AND/OR/NOT circuit using only AND and OR, when all gates have fan-in at most two and each gate costs one. For every nonconstant function in this set, even allowing free inversions on every wire and on the output leaves the minimum binary gate count unchanged. There is one output, and an earlier gate may feed arbitrarily many later gates.

| Minimum paid gates | Labelled functions |
|---:|---:|
| 0 | 6 |
| 1 | 21 |
| 2 | 80 |
| 3 | 260 |
| 4 | 542 |
| 5 | 820 |
| 6 | 1,860 |
| 7 | 1,664 |
| 8 | 1,835 |
| 9 | 410 |
| 10 | 83 |
| **Total** | **7,581** |

The six functions of size zero are the five projections and constant false, which the project defines as the value of a missing output wire. Constant true requires one empty AND. A zero-gate ordinary circuit outputs either a projection or false. The free-inversion conclusion above is stated for nonconstant functions so that the constant convention does not affect it.

The 83 functions at size ten form four permutation-and-duality classes. Their representatives and labelled multiplicities are `e8808000` (2), `eae8e880` (60), `eee8e880` (20) and `fee8e880` (1). The last function is five-input majority. The ten-gate circuit in the last witness row can be checked directly on all 32 assignments. The project's accepted L-meta-1433 also contains a ten-gate construction and a lower bound of ten in its paid-gate basis. The older Rutgers manuscript reports thirteen for this particular monotone function. The constructions here and in L-meta-1433 give explicit shorter programs in the binary AND/OR basis. [Accepted Lean proof](https://github.com/brilliant-hq/pequalnp-proofs/blob/203efb4b463a58b4e677b3c6f554ddca5ad0e4ab/lean/PEqualNP/Outside/L_meta_1433.lean) · [Seidler, Table 5 and following paragraph](https://sites.math.rutgers.edu/~bas312/Research/slp/SLP.pdf)

## Proof by finite exhaustion

Generate the monotone tables recursively using all ordered pairs of monotone restrictions with the low restriction pointwise below the high one. Of these tables, 6,894 depend on all five coordinates. They form 95 classes under input permutations and the duality that complements both the inputs and the output. A monotone circuit transports under duality by interchanging AND and OR. For the project conventions on missing wires the transformation is proved in [Symmetry.lean](Symmetry.lean). In the signed model, reordering or complementing input wires and complementing the output cost nothing. For the remaining 685 nonconstant tables, identifying ignored inputs with an essential input reduces the problem to 16 smaller classes, as described in [the five-input reduction](README.md).

For each representative let $m$ be the size of the exhibited monotone circuit. Evaluate the circuit on every assignment, then exhaust the signed model through $m-1$ binary gates. Free inversions can simulate every paid NOT by changing a wire sign. The signed lower bound and the monotone upper construction therefore give the common minimum. This proof can be replayed independently of the fifteen one-NOT shard theorems.

In signed mode a wire is stored with the sign that makes it false at the all-zero assignment. Any AND/OR of two signed wires, after normalizing its output sign, is one of four functions, namely `a & b`, `a | b`, `a & ~b`, and `~a & b`. Constants and unary gates simplify away for nonconstant targets. A binary gate on two copies of the same signed signal simplifies to a constant or an existing signal. Any duplicate of an available signal can be replaced by that signal, since fan-out is unrestricted. Each nonconstant monotone target has the stored sign.

In a smallest straight-line program erase all unused gates. Just before each gate keep exactly the signals still needed by that gate, the suffix, or its output. All essential inputs are initially live. A gate uses two live operands and produces a new signal. It can discard only operands whose last use is this gate. The four choices for retaining or dropping the operands therefore enumerate all possible lifetimes. The live count can fall by at most one per binary gate. With $r$ gates left a necessary condition is at most $r+1$ live wires. Additionally each positive/negative pair of assignments must still have different live vectors. If those vectors coincide, every deterministic suffix agrees on the pair. These conditions justify the two pruning rules in the lower-bound search.

[search.cpp](search.cpp) uses 32-bit truth tables, scans positive assignments and checks which negative assignments still agree with them. [all_five.py](all_five.py) implements a second search using integer masks for separated pairs and memoized sorted live sets. Both follow the preceding finite-search proof. [optima.txt](optima.txt) records the 95 fully dependent representatives, the number of labelled tables each represents, and a monotone witness with zero-based wire numbers. A line beginning with `80000000` represents the five-way conjunction. The witnesses and minima in this file can all be regenerated from scratch.

## Reproduction

Run in this directory with Python 3.9 or later and a C++17 compiler.

```sh
c++ -std=c++17 -O3 -Wall -Wextra search.cpp -o /tmp/five-input-search
python3 verify_unrestricted.py /tmp/five-input-search > /tmp/five-input-optima.txt
diff -u optima.txt /tmp/five-input-optima.txt
```

Add `--cross-check` to replay the signed lower bounds with the second implementation as well. To replay all 95 five-variable upper witnesses in the project Lean kernel, run the following in this directory.

```sh
python3 kernel_upper.py optima.txt > /tmp/FiveInputUpper.lean
cd ../../lean
lake build PEqualNP.Defs.CircuitLowerBounds
lake env lean --root=/tmp /tmp/FiveInputUpper.lean
```

The generated Lean theorems are named `FiveInputUpper.upper_<hexadecimal table>`. Each states the number of gates, the allowed operations and fan-in, and correctness for every input in the project circuit semantics. The lower bounds and orbit counts use finite external enumeration.
