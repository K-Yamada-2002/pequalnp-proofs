"""Check closure of the supplied lower-bound certificates without calling the search."""
import argparse
from functools import cache
import gzip
from itertools import combinations
from pathlib import Path

from graphs import GRAPHS


def verify(path):
    with gzip.open(path, "rt", encoding="ascii") as rows:
        name, header_budget = next(rows).split()
        n, edges, minimum = GRAPHS[name]
        budget = int(header_budget)
        if budget != minimum - 1:
            raise ValueError("unexpected budget")

        edge_masks = [(1 << a) | (1 << b) for a, b in edges]
        independent = [x for x in range(1 << n) if all(x & e != e for e in edge_masks)]
        maximal = [x for x in independent if not any(x != y and x & y == x for y in independent)]
        assignments = edge_masks + maximal
        target = (1 << len(edges)) - 1
        root = tuple(sorted(sum(((x >> i) & 1) << j for j, x in enumerate(assignments)) for i in range(n)))
        layers = [set() for _ in range(budget + 1)]
        for row in rows:
            remaining, *w = map(int, row.split())
            if not 1 <= remaining <= budget or not 1 <= len(w) <= remaining + 1:
                raise ValueError("invalid layer or width")
            if w != sorted(set(w)) or not (0 <= w[0] and w[-1] < 1 << len(assignments)) or target in w:
                raise ValueError("invalid wire signatures")
            layers[remaining].add(tuple(w))

    if root not in layers[budget]:
        raise ValueError("missing initial state")

    pairs = [(i, j) for i in range(len(edges)) for j in range(len(edges), len(assignments))]
    required = (1 << len(pairs)) - 1

    @cache
    def coverage(wire):
        return sum(1 << k for k, (i, j) in enumerate(pairs) if wire & (1 << i) and not wire & (1 << j))

    for remaining in range(1, budget + 1):
        for wires in layers[remaining]:
            for a, b in combinations(wires, 2):
                unchanged = tuple(w for w in wires if w != a and w != b)
                base = 0
                for wire in unchanged:
                    base |= coverage(wire)
                for result in (a | b, a & b):
                    if result in wires:
                        continue
                    for kept in ((), (a,), (b,), (a, b)):
                        if len(unchanged) + len(kept) + 1 > remaining:
                            continue
                        cover = base | coverage(result)
                        for wire in kept:
                            cover |= coverage(wire)
                        if cover != required:
                            continue
                        if result == target:
                            raise ValueError("reachable output at a listed state")
                        if remaining > 1:
                            successor = tuple(sorted((*unchanged, result, *kept)))
                            if successor not in layers[remaining - 1]:
                                raise ValueError(f"missing successor at layer {remaining - 1}: {successor}")
    print(f"{name}: VERIFIED, budget {budget}, {sum(map(len, layers))} listed states")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", type=Path, nargs="*")
    files = parser.parse_args().files
    for path in files or [Path(__file__).parent / "certificates" / f"{g}.txt.gz" for g in GRAPHS]:
        verify(path)
