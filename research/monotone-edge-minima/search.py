"""Synthesize a circuit on the monotone boundary, or export an exhaustive certificate."""
import argparse
from functools import cache
import gzip
from itertools import combinations
from pathlib import Path

from graphs import GRAPHS, boundary


def run(name, budget, certificate):
    n, edges, _ = GRAPHS[name]
    pos, neg, inputs = boundary(n, edges)
    target = (1 << len(pos)) - 1
    negative_bits = (1 << len(neg)) - 1
    all_pairs = (1 << (len(pos) * len(neg))) - 1
    rejected = set()
    path = {}

    @cache
    def separates(wire):
        absent = ~(wire >> len(pos)) & negative_bits
        return sum(absent << (len(neg) * i) for i in range(len(pos)) if wire & (1 << i))

    @cache
    def possible(wires, remaining):
        if target in wires:
            return True
        if remaining == 0 or len(wires) > remaining + 1:
            return False
        for i, j in combinations(range(len(wires)), 2):
            a, b = wires[i], wires[j]
            rest = wires[:i] + wires[i+1:j] + wires[j+1:]
            covered = 0
            for wire in rest:
                covered |= separates(wire)
            for value in (a & b, a | b):
                if value in wires:
                    continue
                for saved in ((), (a,), (b,), (a, b)):
                    if len(rest) + len(saved) + 1 > remaining:
                        continue
                    cover = covered | separates(value)
                    for wire in saved:
                        cover |= separates(wire)
                    if cover != all_pairs:
                        continue
                    nxt = tuple(sorted((*rest, *saved, value)))
                    if possible(nxt, remaining-1):
                        path[wires, remaining] = (a, b, value, nxt)
                        return True
        if certificate is not None:
            rejected.add((remaining, wires))
        return False

    found = possible(inputs, budget)
    print(name, budget, "SAT" if found else "UNSAT", "states", possible.cache_info().misses)
    if found:
        signatures = [sum(1 << j for j, x in enumerate(pos + neg) if (x >> i) & 1) for i in range(n)]
        circuit = []
        wires, remaining = inputs, budget
        while target not in wires:
            a, b, value, wires = path[wires, remaining]
            circuit.append(("and" if value == a & b else "or", signatures.index(a), signatures.index(b)))
            signatures.append(value)
            remaining -= 1
        output = signatures.index(target)
        for x in range(1 << n):
            ws = [bool((x >> i) & 1) for i in range(n)]
            for op, a, b in circuit:
                ws.append((ws[a] and ws[b]) if op == "and" else (ws[a] or ws[b]))
            if ws[output] != any(x & p == p for p in pos):
                raise ValueError("candidate failed its full truth table")
        print("verified on", 1 << n, "assignments:", circuit, "output", output)
    elif certificate is not None:
        # Each row contains remaining gates followed by the sorted wire signatures.
        with certificate.open("wb") as raw, gzip.GzipFile(filename="", fileobj=raw, mode="wb", mtime=0) as f:
            f.write(f"{name} {budget}\n".encode())
            for remaining, wires in sorted(rejected):
                f.write((" ".join(map(str, (remaining, *wires))) + "\n").encode())


if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("graph", choices=GRAPHS)
    p.add_argument("budget", type=int)
    p.add_argument("--certificate", type=Path)
    args = p.parse_args()
    run(args.graph, args.budget, args.certificate)
