# Pivotal inputs in the projective-plane circuit problem

These files establish partial lower bounds for the official problem L-meta-1629. In a plane of order $q$, write $N=q^2+q+1$. A monotone fan-in-two circuit accepts each incident point-line pair and rejects independent inputs with at most $q$ lines on. The target $Nq\le 100\,|C|$ remains open in general.

## A false input forcing many OR gates

For an incident point $o$ and line $l$, activate all points of $l$ other than $o$, and all lines through $o$ other than $l$. Both masks have size $q$. The input is independent. Every inactive point lies on an active line, and every inactive line contains an active point. Turning on any one of the $2(N-q)=2(q^2+1)$ missing coordinates therefore makes the output true. This includes an added line taking the mask above the promise. Acceptance there follows from monotonicity and the contained incident pair.

At a fixed rejected input, label each wire by the set of single-coordinate additions that make it switch from false to true. An AND output inherits all its switches from any operand initially false. A binary OR may take a union of two sets. Starting from singletons and empty sets, obtaining a wire with $s$ switches requires at least $s-1$ OR positions, even with shared wires. The invariant for every family $F$ of wire labels is

$$
  |\bigcup F|\le |F|+\text{number of OR gates processed}.
$$

Replacing a new label by its one or two parents proves the inductive step. Hence at least $2q^2+1$ OR gates occur. The hypotheses on incidence are exactly the degree and unique-join hypotheses of the official problem. The proof derives point degree and line intersection. In particular the official numerical target follows for $2\le q\le198$, since $(q^2+q+1)q\le100(2q^2+1)$ in that range.

## A false positive forcing many AND gates

Fix any point mask $X$ and an independent assignment accepted by the circuit. Among its accepted submasks of lines, choose one $T$ of minimum cardinality. Then $|T|>q$, and deleting any one line of $T$ changes the output from true to false. For a wire, track the set of line deletions producing such a change, always using the same baseline $X,T$. Charge a gate one unit if its output has a nonempty set of pivotal deletions contained in neither operand individually. OR gates cost zero. A charged gate must be a binary AND with incomparable operand sets. The same union invariant implies $|T|\le1+\text{charge}$, so at least $q$ distinct AND positions are charged on this one baseline. This holds for arbitrary incidence relations. A strict charge cap below $q$ on every independent submask implies global soundness there.

The coefficient is sharp for this local argument. Starting with the direct OR of all incident-pair ANDs, append the disjunction with the conjunction of $q+1$ fixed distinct line variables. The added term vanishes on all promised inputs. With all points off and exactly those lines on, a binary chain for the conjunction incurs exactly $q$ charged gates. No incidence gate is charged there.

## Reproduction

The five Lean files use Lean 4.36.0 and the public definitions at upstream commit `8216299`. From the upstream project's `lean` directory, build the definitions and run the replay script in this directory.

```sh
lake build PEqualNP.Defs
lake env bash ../notes/plane-pivotal-gates/replay.sh
```

The script compiles all five files, reports the axioms of the main results, and runs independent finite checks. It uses a temporary output directory. For orders 2, 3 and 5, the Python checks visit respectively 21, 52 and 186 incident flags, and the explicit circuit incurs respectively 2, 3 and 5 AND charges. For order 2 it also compares the circuit to incidence on all 3,712 promised assignments.

The unconditional theorem is `PlaneLocalPrice.pencil_or_lower` in `PencilPrice.lean`. Its public-constants formulation `pencil_child` counts OR gates by their output on the mixed input list `[true, false]`; on the allowed basis only OR returns true. The independent-error theorem is `PlaneLocalPrice.sparse_failure` in `SparseFailure.lean`. `LocalPrice.lean` and `UpwardPrice.lean` prove the circuit counting bounds. `Pencil.lean` supplies the finite incidence geometry. Counts from different baselines can overlap. Obtaining a uniform lower bound of order $Nq$ for all orders is still open.
