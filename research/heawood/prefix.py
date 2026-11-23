"""Check short prefixes against induced-graph lower bounds using scalar gate counts."""
from functools import cache
from itertools import combinations, product

from make_instance import automorphisms
from restrict import EDGES, FULL, lower, vertices


def check(mask, budget, depth):
    vertices_left = vertices(mask)
    edges = [1 << a | 1 << b for a, b in EDGES if a in vertices_left and b in vertices_left]
    target = (1 << len(edges)) - 1
    independent = {s for s in range(mask + 1) if not s & ~mask and all(s & e != e for e in edges)}
    maximal = sorted(s for s in independent if all((s | 1 << i) not in independent
                                                    for i in vertices(mask ^ s)))
    tests = edges + maximal
    negatives = ((1 << len(tests)) - 1) ^ target
    inputs = tuple(sum(1 << j for j, s in enumerate(tests) if s >> i & 1) for i in vertices_left)
    required = (1 << (len(edges) * len(maximal))) - 1

    @cache
    def separates(wire):
        zero = (negatives & ~wire) >> len(edges)
        return sum(zero << (i * len(maximal)) for i in range(len(edges)) if wire >> i & 1)

    projections = []
    for count in (1, 2, 3):
        for subset in combinations(vertices_left, count):
            # Using only same-side triples keeps this finite certificate small.
            if count == 3 and min(subset) < 7 <= max(subset):
                continue
            removed = sum(1 << v for v in subset)
            kept = sum(1 << j for j, e in enumerate(edges) if not e & removed)
            if kept:
                slack = budget - lower(mask ^ removed) - sum(not w & kept for w in inputs)
                projections.append((kept, slack))

    dual = list(range(7, 14)) + list(range(7))
    assert {(dual[b], dual[a]) for a, b in EDGES} == set(EDGES)
    group = list(automorphisms())
    group += [[dual[i] for i in g] for g in group]
    stabilizer = [[vertices_left.index(g[v]) for v in vertices_left] for g in group
                  if {g[v] for v in vertices_left} == set(vertices_left)]
    first_pairs = {min(tuple(sorted((g[i], g[j]))) for g in stabilizer)
                   for i, j in combinations(range(len(inputs)), 2)}
    visits = 0

    def excluded(wires, spare, step):
        nonlocal visits
        visits += 1
        if target in wires or step == depth:
            return False
        for i, j in combinations(range(len(wires)), 2):
            if step == 0 and (i, j) not in first_pairs:
                continue
            a, b = wires[i], wires[j]
            rest = wires[:i] + wires[i+1:j] + wires[j+1:]
            untouched = 0
            for wire in rest:
                untouched |= separates(wire)
            for is_or, value in ((False, a & b), (True, a | b)):
                if not value & target or value & negatives == negatives:
                    continue
                if any(not (value & target & ~old or old & negatives & ~value) for old in inputs + wires):
                    continue
                for keep_a, keep_b in product((False, True), repeat=2):
                    saved = ((a,) if keep_a else ()) + ((b,) if keep_b else ())
                    if len(rest) + 1 + len(saved) > budget - step:
                        continue
                    covered = untouched | separates(value)
                    for old in saved:
                        covered |= separates(old)
                    if covered != required:
                        continue
                    child = []
                    for (kept, _), limit in zip(projections, spare):
                        left, right, out = a & kept, b & kept, value & kept
                        removable = not left or not right or not out or (is_or and out in (left, right))
                        # Available budget loses one for an eliminated gate and for a new live zero.
                        # A zero operand on its last use is no longer a live zero after the gate.
                        slack = limit - int(removable) - int(not out)
                        slack += int(not keep_a and not left) + int(not keep_b and not right)
                        if slack < 0:
                            break
                        child.append(slack)
                    if len(child) == len(projections) and not excluded((*rest, value, *saved), child, step + 1):
                        return False
        return True

    spare = [limit for _, limit in projections]
    closed = min(spare) < 0 or excluded(inputs, spare, 0)
    return closed, visits


if __name__ == '__main__':
    for name, mask, budget, depth in [('six points', FULL ^ (1 << 6), 19, 6), ('full graph', FULL, 21, 2)]:
        closed, visits = check(mask, budget, depth)
        print(name, 'budget', budget, 'depth', depth, 'EXCLUDED' if closed else 'SURVIVING PREFIX',
              'visited prefixes', visits)
        if not closed:
            raise SystemExit(1)
