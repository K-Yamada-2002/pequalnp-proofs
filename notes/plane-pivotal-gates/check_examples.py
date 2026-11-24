"""Independent finite checks of the flag masks and the sharp AND charge example."""
from itertools import product


def projective_plane(prime):
    # A point and a line are normalized triples. A zero dot product is incidence.
    triples = [v for v in product(range(prime), repeat=3)
               if next((x for x in v if x), 0) == 1]
    return [frozenset(i for i, p in enumerate(triples)
                      if sum(a * b for a, b in zip(p, line)) % prime == 0)
            for line in triples]


def circuit(lines, order):
    n = len(lines)
    gates = []

    def gate(op, left, right):
        gates.append((op, left, right))
        return 2 * n + len(gates) - 1

    def fold(op, wires):
        it = iter(wires)
        wire = next(it)
        for other in it:
            wire = gate(op, wire, other)
        return wire

    exact = fold("or", [gate("and", p, n + l)
                        for l, points in enumerate(lines) for p in sorted(points)])
    extra = fold("and", range(n, n + order + 1))
    gate("or", exact, extra)
    return gates


def evaluate(gates, bits):
    wires = list(bits)
    for op, i, j in gates:
        wires.append((wires[i] and wires[j]) if op == "and" else (wires[i] or wires[j]))
    return wires


def check(q):
    lines = projective_plane(q)
    n = len(lines)
    assert n == q*q + q + 1
    flags = 0
    for l, points in enumerate(lines):
        for o in points:
            x = points - {o}
            b = {m for m in range(n) if m != l and o in lines[m]}
            covered_points = set().union(*(lines[m] for m in b))
            hit_lines = {m for m in range(n) if lines[m] & x}
            assert len(x) == len(b) == q
            assert covered_points == set(range(n)) - x
            assert hit_lines == set(range(n)) - b
            assert len(covered_points) + len(hit_lines) == 2*(q*q + 1)
            flags += 1

    gates = circuit(lines, q)
    selected = set(range(q+1))

    def bits(b):
        return [False]*n + [m in b for m in range(n)]

    base = evaluate(gates, bits(selected))
    after = [evaluate(gates, bits(selected - {m})) for m in range(n)]
    pivots = [{m for m, test in enumerate(after) if v and not test[k]}
              for k, v in enumerate(base)]
    paid = [(op, k) for k, (op, i, j) in enumerate(gates, 2*n)
            if pivots[k] - pivots[i] and pivots[k] - pivots[j]]
    assert base[-1] and pivots[-1] == selected
    assert len(paid) == q and all(op == "and" for op, _ in paid)
    print(f"q={q}, flags={flags}, upward pivots per flag={2*(q*q+1)}, paid ANDs={len(paid)}")

    if q == 2:
        checked = 0
        for inputs in product((False, True), repeat=2*n):
            active = [m for m in range(n) if inputs[n+m]]
            if len(active) <= q:
                assert evaluate(gates, inputs)[-1] == any(
                    inputs[p] for m in active for p in lines[m])
                checked += 1
        print(f"Fano promise assignments checked={checked}")


if __name__ == "__main__":
    for order in (2, 3, 5):
        check(order)
