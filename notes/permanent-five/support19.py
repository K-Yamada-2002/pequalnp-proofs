"""Classify 19-cell supports under independent row and column permutations."""
from collections import Counter
from itertools import combinations_with_replacement, permutations
from math import comb, factorial, prod
from sage.all import QQ, matrix

ROWS = COLS = 5


def support_representatives():
    permutations_of_mask = []
    for order in permutations(range(COLS)):
        permutations_of_mask.append([
            sum(1 << order[j] for j in range(COLS) if mask & (1 << j))
            for mask in range(1 << COLS)])
    seen = set()
    for rows in combinations_with_replacement(range(1 << COLS), ROWS):
        if rows not in seen:
            orbit = {tuple(sorted(perm[r] for r in rows)) for perm in permutations_of_mask}
            seen.update(orbit)
            row_orders = factorial(ROWS) // prod(factorial(n) for n in Counter(rows).values())
            yield rows, len(orbit) * row_orders


def quadratic_data(rows):
    cells = [(i, j) for i, row in enumerate(rows) for j in range(COLS) if row & (1 << j)]
    if not cells:
        return cells, matrix(QQ, 0, 0)
    def disjoint(s, t):
        return int(s[0] != t[0] and s[1] != t[1])
    # Use differences e_i-e_last as a basis of the total-sum-zero hyperplane.
    h = len(cells)-1
    last = cells[-1]
    polar = matrix(QQ, h, h, lambda i, j: disjoint(cells[i], cells[j])
                   - disjoint(cells[i], last) - disjoint(last, cells[j]))
    return cells, polar


if __name__ == "__main__":
    counts = Counter()
    exceptional = []
    labelled = 0
    for rows, size in support_representatives():
        if sum(row.bit_count() for row in rows) == 19:
            _, polar = quadratic_data(rows)
            rank = polar.rank()
            counts[rank] += 1
            labelled += size
            if rank < 18:
                exceptional.append((rows, size))
    assert labelled == comb(25, 19)
    assert counts == {17: 1, 18: 68}
    assert exceptional == [((3, 29, 29, 29, 31), 400)]
    print("Rank counts:", dict(counts), "Exceptional orbit:", exceptional)
