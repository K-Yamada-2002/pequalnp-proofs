"""Exact weighted synthesis for the bowtie graph, with singleton-aware wire tables."""
from functools import cache
from itertools import combinations
import sys

N = 5
EDGES = ((0, 1), (0, 2), (1, 2), (0, 3), (0, 4), (3, 4))
POS = tuple((1 << a) | (1 << b) for a, b in EDGES)


def truth(s):
    return any(s & p == p for p in POS)


NEG = tuple(s for s in range(1 << N) if not truth(s)
            and all(truth(s | (1 << i)) for i in range(N) if not s >> i & 1))
SAMPLES = tuple(dict.fromkeys((*POS, *NEG, *(1 << i for i in range(N)))))
INPUTS = tuple(sum(1 << k for k, s in enumerate(SAMPLES) if s >> i & 1)
               for i in range(N))
TARGET = (1 << len(POS)) - 1
SINGLETONS = sum(1 << SAMPLES.index(1 << i) for i in range(N))
REQUIRED = (1 << (len(POS) * len(NEG))) - 1


@cache
def separates(w):
    """Pairs of a positive and a maximal negative distinguished in the needed direction."""
    return sum(1 << (i * len(NEG) + j) for i in range(len(POS)) if w >> i & 1
               for j in range(len(NEG)) if not w >> (len(POS) + j) & 1)


def search(limit):
    choices = {}

    @cache
    def possible(wires, remaining):
        if TARGET in wires:
            return True
        if remaining < max(1, len(wires) - 1):
            return False
        for i, j in combinations(range(len(wires)), 2):
            a, b = wires[i], wires[j]
            rest = wires[:i] + wires[i+1:j] + wires[j+1:]
            for op, c in (("and", a & b), ("or", a | b)):
                if c in wires:
                    continue
                cost = 1 + (op == "or" and (c & SINGLETONS).bit_count() < 2)
                after = remaining - cost
                for kept in ((), (a,), (b,), (a, b)):
                    if len(rest) + len(kept) > after:
                        continue
                    nxt = tuple(sorted((*rest, *kept, c)))
                    cover = 0
                    for w in nxt:
                        cover |= separates(w)
                    if cover == REQUIRED and possible(nxt, after):
                        choices[wires, remaining] = (op, a, b, c, nxt, after)
                        return True
        return False

    wires = tuple(sorted(INPUTS))
    found = possible(wires, limit)
    print("budget", limit, "SAT" if found else "UNSAT",
          "distinct states", possible.cache_info().misses, flush=True)
    if found:
        refs, net, left = {v: i for i, v in enumerate(INPUTS)}, [], limit
        while TARGET not in wires:
            op, a, b, c, wires, left = choices[wires, left]
            net.append((op, refs[a], refs[b]))
            refs[c] = N + len(net) - 1
        costs = []
        for s in range(1 << N):
            values = [bool(s >> i & 1) for i in range(N)]
            for op, a, b in net:
                values.append(values[a] and values[b] if op == "and" else values[a] or values[b])
            assert values[refs[TARGET]] == truth(s)
            if s.bit_count() == 1:
                costs.append(values[N:])
        weight = len(net) + sum(op == "or" and sum(col) < 2
                                for (op, _, _), col in zip(net, zip(*costs)))
        assert weight == limit - left
        print("all 32 inputs verified, weight", weight, "gates", net, "output", refs[TARGET])
    return found


if __name__ == "__main__":
    for limit in map(int, sys.argv[1:]):
        search(limit)
