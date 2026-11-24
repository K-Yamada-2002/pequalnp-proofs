"""Exact obstructions to a seven-plane on nine additional 15-cell supports."""
import argparse
from itertools import combinations, permutations
from math import comb, factorial, prod

from sage.all import GF, QQ, PolynomialRing, matrix, vector
from support_bound import support_representatives


# Each tuple lists the supported columns as a five-bit mask for each row.
UNIT_CASES = {
    (3, 28, 31, 31): 13, (3, 15, 23, 31): 13, (3, 15, 29, 31): 13,
    (3, 29, 30, 31): 13, (7, 7, 27, 31): 13, (7, 11, 23, 31): 7,
    (7, 11, 29, 31): 13, (7, 15, 25, 31): 13, (7, 25, 30, 31): 13,
}


class MatchingForms:
    def __init__(self, rows, field):
        self.cells = [(r, c) for r, mask in enumerate(rows) for c in range(5) if mask & (1 << c)]
        assert len(self.cells) == 15
        self.matchings = {}
        for degree in (2, 3, 4):
            self.matchings[degree] = [
                indices for indices in combinations(range(15), degree)
                if all(self.cells[i][0] != self.cells[j][0] and self.cells[i][1] != self.cells[j][1]
                       for i, j in combinations(indices, 2))
            ]
        self.difference = matrix.identity(field, 14).stack(matrix(field, 1, 14, [-1]*14))
        # Each quadratic matching contributes a one in both off-diagonal positions.
        raw = matrix(field, 15, 15)
        for i, j in self.matchings[2]:
            raw[i, j] = raw[j, i] = 1
        restricted = self.difference.transpose() * raw * self.difference
        assert restricted.is_invertible()
        self.inverse = restricted.inverse()

    def value(self, entries, degree):
        return sum(prod(entries[i] for i in indices) for indices in self.matchings[degree])

    def normal(self, entries, degree):
        # The columns of difference are e_i - e_last in the total-sum-zero hyperplane.
        ring = entries.base_ring()
        grad = vector(ring, 15)
        for indices in self.matchings[degree]:
            for j in indices:
                grad[j] += prod(entries[i] for i in indices if i != j)
        return self.difference * (self.inverse * (self.difference.transpose() * grad))

    def cross_check(self):
        # Enumerate the original 120 injections independently, before collecting terms.
        # Each partial matching of size d occurs (5-d)! times in that expansion.
        counts = {d: {} for d in (2, 3, 4)}
        index = {cell: i for i, cell in enumerate(self.cells)}
        for columns in permutations(range(5), 4):
            selected = [index[r, c] for r, c in enumerate(columns) if (r, c) in index]
            for degree, terms in counts.items():
                for subset in combinations(selected, degree):
                    terms[subset] = terms.get(subset, 0) + 1
        for degree, terms in counts.items():
            assert terms == dict.fromkeys(self.matchings[degree], factorial(5-degree))


def check(rows, field):
    forms = MatchingForms(rows, field)
    forms.cross_check()
    ring = PolynomialRing(field, 4, 'a', order='degrevlex')
    row = rows.index(31)
    weights = [*ring.gens(), 1-sum(ring.gens())]
    functional = vector(ring, [weights[j] if i == row else 0 for i, j in forms.cells])
    z = forms.difference * (forms.inverse * (forms.difference.transpose() * functional))
    first = ring.ideal([forms.value(z, d) for d in (2, 3, 4)]).groebner_basis()
    u, v = (forms.normal(z, d) for d in (3, 4))
    equations = [forms.value(w, 2) for w in (u, v, u+v)]
    basis = ring.ideal(list(first) + equations).groebner_basis()
    assert list(basis) == [ring.one()]
    print(rows, field, 'unit ideal', flush=True)


def report_coverage():
    earlier = {(0, 31, 31, 31), (1, 15, 31, 31), (1, 30, 31, 31),
               (3, 7, 31, 31), (7, 7, 15, 31)}
    new = set(UNIT_CASES)
    orbits = {rows: size for rows, size in support_representatives()
              if sum(mask.bit_count() for mask in rows) == 15}
    assert len(orbits) == 27 and sum(orbits.values()) == comb(20, 15)
    assert earlier.isdisjoint(new) and earlier | new <= orbits.keys()
    remaining = orbits.keys() - earlier - new
    for label, group in [('earlier', earlier), ('new', new), ('remaining', remaining)]:
        print(label, len(group), 'orbits,', sum(orbits[rows] for rows in group), 'labelled supports')
    print('Remaining row masks:', sorted(remaining))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--rational', action='store_true', help='run all nine tests in characteristic zero')
    args = parser.parse_args()
    for rows, prime in UNIT_CASES.items():
        check(rows, QQ if args.rational else GF(prime))
    report_coverage()
