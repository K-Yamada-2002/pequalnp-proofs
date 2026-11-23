"""Necessary seven-plane test for a 15-cell support, by reduction along one row."""
from itertools import combinations, combinations_with_replacement, product
from math import prod
import argparse
from sage.all import GF, PolynomialRing, matrix


def chart_test(rows, primes):
    positions = [(i, j) for i, mask in enumerate(rows) for j in range(5) if mask >> j & 1]
    cols = [j for i, j in positions if i == 3]
    other = [p for p in positions if p[0] != 3]
    assert len(positions) == 15
    k = 8-len(cols)
    all_positions = other+[(3, j) for j in cols]
    matchings = {d: [inds for inds in combinations(range(15), d)
                     if len({all_positions[i][0] for i in inds}) == d
                     and len({all_positions[i][1] for i in inds}) == d] for d in (2, 3, 4)}

    def eval_term(v, z, degree):
        entries = list(v)+list(z)+[-sum(v)-sum(z)]
        return sum(prod(entries[i] for i in indices) for indices in matchings[degree])

    def quadratic(v):
        return eval_term(v, [0]*(len(cols)-1), 2)

    def polar(v, w):
        return quadratic(v+w)-quadratic(v)-quadratic(w)

    def split(V, base):
        if V.nrows() == 0:
            return [], []
        x = next((v for v in V if quadratic(v) == 0), None)
        if x is None:
            for ix in combinations(range(V.nrows()), min(3, V.nrows())):
                for coeff in product(base, repeat=len(ix)-1):
                    v = V[ix[0]] + sum((t*V[j] for t, j in zip(coeff, ix[1:])), 0*V[ix[0]])
                    if quadratic(v) == 0:
                        x = v
                        break
                if x is not None:
                    break
        if x is None:
            raise ValueError("no isotropic vector in this diagonal block")
        y = next(v for v in V if polar(x,v))
        y = y/polar(x,y)
        y = y-quadratic(y)*x
        ortho = matrix(base, [[polar(z,v) for v in V] for z in (x,y)])
        X, Y = split(ortho.right_kernel().basis_matrix()*V, base)
        return [x]+X, [y]+Y

    # Choose a prime where this even-dimensional quotient already splits.
    # The equations are integral, and the original plane specializes before reduction.
    for prime in primes:
        field = GF(prime)
        H = matrix(field, len(cols)-1, len(other),
                   lambda i,j: int(other[j][1] == cols[i])-int(other[j][1] == cols[-1]))
        V = H.right_kernel().basis_matrix()
        assert V.nrows() == 2*k
        det = matrix(field, [[polar(a,b) for b in V] for a in V]).det()
        if det and ((-1)**k*det).is_square():
            break
    else:
        raise ValueError("no split prime among those tested")
    X, Y = split(V, field)
    print(rows, "prime", prime, flush=True)
    assert all(polar(v,w)==0 for family in (X,Y) for v in family for w in family)
    assert matrix(field, [[polar(x,y) for y in Y] for x in X]) == matrix.identity(field, k)

    pairs = list(combinations(range(k), 2))
    names = [f"s{i}{j}" for i,j in pairs]+[f"u{i}{j}" for i in range(k) for j in cols[:-1]]
    ring = PolynomialRing(field, names, order="degrevlex")
    skew = matrix(ring, k, k)
    for (i,j), v in zip(pairs, ring.gens()):
        skew[i,j], skew[j,i] = v, -v
    row_lifts = matrix(ring, k, len(cols)-1, ring.gens()[len(pairs):])
    for flip in product((0,1), repeat=k):
        left = matrix(ring, [Y[i] if v else X[i] for i,v in enumerate(flip)])
        right = matrix(ring, [X[i] if v else Y[i] for i,v in enumerate(flip)])
        plane = left+skew*right
        eqs = []
        for d in (3,4):
            for inds in combinations_with_replacement(range(k),d):
                eqs.append(eval_term(sum(plane[i] for i in inds), sum(row_lifts[i] for i in inds), d))
        # A consistent special fiber of these necessary equations makes the
        # unit-ideal test inconclusive. This inexpensive check can save a large basis.
        # Compute the affine system in the lift variables at the chart origin.
        coeff = matrix(field, len(eqs), k*(len(cols)-1))
        rhs = []
        for h, equation in enumerate(eqs):
            rhs.append(-equation.constant_coefficient())
            for j, var in enumerate(ring.gens()[len(pairs):]):
                coeff[h,j] = equation.monomial_coefficient(var)
        if coeff.rank() == coeff.augment(matrix(field, len(eqs), 1, rhs)).rank():
            print(rows, "inconclusive at chart origin", flip, flush=True)
            return
        gb = ring.ideal(eqs).groebner_basis(algorithm="libsingular:slimgb")
        if list(gb) != [ring.one()]:
            print(rows, "inconclusive chart", flip, flush=True)
            return
        print(rows, "unit ideal", flip, flush=True)
    print(rows, "excluded", flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("supports", nargs="+", help="comma-separated row masks, e.g. 3,7,31,31")
    parser.add_argument("--prime", type=int, choices=(5,7,11,13,17,19,23,29,31))
    args = parser.parse_args()
    primes = [args.prime] if args.prime else (5,7,11,13,17,19,23,29,31)
    for arg in args.supports:
        chart_test(tuple(map(int, arg.split(","))), primes)
