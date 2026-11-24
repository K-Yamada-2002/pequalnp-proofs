# One NOT cannot save a gate on a five-input monotone output

For every monotone Boolean function on five labelled inputs, a binary AND/OR circuit achieves the same minimum gate count as a binary AND/OR/NOT circuit allowed at most one NOT. There are 7,581 such functions. This result concerns a single output and counts each gate once, even when later gates reuse it.

The circuit semantics are those of `PEqualNP.CircuitLowerBounds`. A gate may have zero, one or two operands. An empty AND returns true, an empty OR returns false, NOT uses its first operand and defaults to true, and an out-of-range wire reads false.

## Functions that depend on all five inputs

At upstream commit [203efb4](https://github.com/brilliant-hq/pequalnp-proofs/tree/203efb4b463a58b4e677b3c6f554ddca5ad0e4ab/lean/PEqualNP/Outside), each of the 15 accepted shards listed in [all_five.py](all_five.py) supplies the replacement theorem for ten specified truth tables. For example, [L-meta-1429](https://github.com/brilliant-hq/pequalnp-proofs/blob/203efb4b463a58b4e677b3c6f554ddca5ad0e4ab/lean/PEqualNP/Outside/L_meta_1429.lean) proves that any admissible circuit for one of its ten functions can be replaced by an AND/OR circuit of at most the same size. We use the union of the shards and allow overlaps.

Two transformations extend each replacement result.

* **Permuting inputs.** Relabel the first five wire indices in each gate and in the output. Later wire indices, including every out-of-range index, keep their original meanings. The inverse permutation recovers the original function. Gate count and NOT positions are preserved.
* **Dualizing.** For a function $f$ let $f^*(x)=\neg f(\neg x)$. On complementary inputs, arrange for each new wire to be the complement of the old wire. Swap AND and OR when every input wire exists. If an original AND has a missing wire, its dual is a constant true gate. For an original OR, omit missing wires from the dual AND. Retain a NOT on a valid first operand, and replace a NOT with no valid first operand by a constant false gate. These replacements preserve the number of gate positions and can only remove NOTs. A nonconstant output has a valid wire index. Dualization is an involution on functions, so the size bound transfers in both directions.

The Lean proofs [Symmetry.lean](Symmetry.lean) and [OneNot.lean](OneNot.lean) establish the circuit transformations and the transfer of the one-NOT replacement theorem. They work at every input count. The Python verifier independently enumerates all monotone tables, extracts the representatives from the pinned upstream sources, and checks **set equality** between their symmetry closure and the set of tables that depend on all five inputs. That set has 6,894 elements.

## The other 687 functions

A monotone table on $n$ inputs is determined by two monotone tables on $n-1$ inputs, its low and high restrictions. Any pair with the low table pointwise at most the high table gives one such table. Starting with the two constants gives all the tables, with no duplicates. Flipping each input in turn identifies its essential variables.

| Essential variables | Labelled functions on five inputs |
|---:|---:|
| 0 | 2 |
| 1 | 5 |
| 2 | 20 |
| 3 | 90 |
| 4 | 570 |
| 5 | 6,894 |

For a nonconstant function that ignores some inputs, delete those inputs by identifying each with its first essential input. Renumber internal wires by their position in the gate list, and send indices beyond the original circuit to an out-of-range index in the smaller circuit. This preserves the truth function, size, and allowed operations. A circuit on the reduced input set can conversely ignore the extra inputs, shifting its internal indices back. The constant false function can use an out-of-range output and zero gates. Constant true uses one empty AND, and every circuit with zero gates outputs a projection or false.

The 685 nonconstant tables with fewer than five essential inputs reduce to 16 representatives under permutations and dualization. The verifier constructs and replays a monotone circuit for each. For a representative with a construction of size $m>0$, it rules out even $m-1$ binary gates when every wire can be complemented for free. Hence these 685 functions attain the reported minima even with any number of paid NOTs. The zero-gate projection attains its minimum directly.

For the lower bound store each wire up to complementation, choosing the sign that is false on the all-zero assignment. AND and OR acting on either sign of either operand give four possibilities, namely $a\land b$, $a\lor b$, $a\land\neg b$, and $\neg a\land b$. All nonconstant monotone representatives are false on the all-zero assignment. Constants, repeated operands and copies of available signed wires can be eliminated from a minimum circuit for these functions.

At each cut the search keeps the wire functions still needed by a future gate or the output. All essential inputs must start live. It tries each pair of distinct operands, each allowed operation, and all four choices for retaining the two operands after use. An unused gate can be deleted. A pair of assignments with opposite target values must differ on at least one live wire, since a deterministic suffix cannot distinguish identical live vectors. With $r$ gates left at most $r+1$ wires can be live, since a gate reduces the number by at most one on the way to the final output. These are necessary conditions at every cut. Memoization keys include the complete live set and remaining budget.

## Reproduction

Run the verifier from this directory in the research checkout. It requires Python 3.9 or later and Git.

```sh
python3 all_five.py ../..
```

The output includes every smaller representative and its optimum. The accepted shards and the symmetry theorems are Lean proofs. The equality of the finite sets of truth tables and the smaller circuit searches are checked by Python. The combined 7,581-function result is a deduction from those pieces.

To check the two Lean files, run the following from the checkout root with the pinned Lean toolchain and project dependencies available.

```sh
cd lean
lake build PEqualNP.Defs.CircuitLowerBounds
proof_dir=../notes/five-input-one-not
olean_dir=$(mktemp -d)
lake env lean --root="$proof_dir" -o "$olean_dir/Symmetry.olean" "$proof_dir/Symmetry.lean"
lake env sh -c 'export LEAN_PATH="$1:$LEAN_PATH"; exec lean --root="$2" "$2/OneNot.lean"' sh "$olean_dir" "$proof_dir"
```
