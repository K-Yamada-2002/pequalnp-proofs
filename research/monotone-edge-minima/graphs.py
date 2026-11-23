"""Graph labels follow the three desk statements."""
from itertools import combinations

GRAPHS = {
    "cube": (8, [(i, j) for i, j in combinations(range(8), 2) if (i ^ j) in (1, 2, 4)], 13),
    "prism": (6, [(0, 1), (1, 2), (0, 2), (3, 4), (4, 5), (3, 5), (0, 3), (1, 4), (2, 5)], 10),
    "wheel": (6, [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 5), (2, 5), (3, 5), (4, 5)], 11),
}


def boundary(n, edges):
    positive = [(1 << a) | (1 << b) for a, b in edges]

    def contains_edge(x):
        return any(x & p == p for p in positive)

    negative = [x for x in range(1 << n) if not contains_edge(x) and
                all(contains_edge(x | (1 << i)) for i in range(n) if not (x >> i) & 1)]
    inputs = tuple(sorted(sum(1 << j for j, x in enumerate(positive + negative) if (x >> i) & 1)
                          for i in range(n)))
    return positive, negative, inputs
