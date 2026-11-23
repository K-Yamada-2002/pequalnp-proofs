"""Exact quadratic bound on the union of all nonzero matrix positions of L."""
from collections import Counter
from itertools import combinations_with_replacement, permutations
from math import comb, factorial, perm, prod
from sage.all import matrix, PolynomialRing, QQ

ROWS, COLS = 4, 5


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


def radical_obstruction(cells, polar):
    basis = polar.right_kernel().basis()
    if not basis:
        return False
    R = PolynomialRing(QQ, names=tuple(f"r{k}" for k in range(len(basis))))
    values = [sum(x*v[i] for x, v in zip(R.gens(), basis)) for i in range(len(cells)-1)]
    directions = dict(zip(cells, [*values, -sum(values)]))
    permanent = sum(prod(1+directions.get((i,j),0) for i,j in enumerate(cols))
                    for cols in permutations(range(COLS), ROWS))
    return permanent != perm(COLS, ROWS)


if __name__ == "__main__":
    counts = Counter()
    possible = Counter()
    sparse = []
    labelled = Counter()
    for rows, orbit_size in support_representatives():
        weight = sum(r.bit_count() for r in rows)
        counts[weight] += 1
        labelled[weight] += orbit_size
        cells, polar = quadratic_data(rows)
        bound = polar.nrows() - (polar.rank()+1)//2
        if weight == 14 and bound >= 7:
            assert bound == 7
            sparse.append((rows, polar.nullity(), radical_obstruction(cells, polar)))
        if bound >= 7:
            possible[weight] += 1
    assert all(labelled[n] == comb(ROWS*COLS, n) for n in range(ROWS*COLS+1))
    print("nonzero_positions support_orbits orbits_passing_quadratic_bound")
    for n in sorted(counts):
        print(n, counts[n], possible[n])
    print("14-position representatives: row masks, radical dimension, radical obstruction")
    for result in sparse:
        print(*result)
