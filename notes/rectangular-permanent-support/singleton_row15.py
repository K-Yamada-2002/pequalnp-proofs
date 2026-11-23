"""Test the reduced cubic on every hyperbolic chart, over the field of 13 elements."""
from itertools import combinations, product
from sage.all import GF, PolynomialRing, matrix, vector

K = GF(13)


def reduced_case(full_first_column):
    n = 4 if full_first_column else 5
    basis = matrix.identity(K, 2*n)
    if full_first_column:
        def unpack(v):
            a = vector([v[0], v[1], -v[0]-v[1], 0])
            b = vector([*v[2:5], -sum(v[2:5])])-a
            c = vector([*v[5:8], -sum(v[5:8])])-a
            return a, b, c

        w = K(3)
        assert w**2+w+1 == 0
        X = [basis[0]+w*basis[1], *basis[2:5]]
        Y = [basis[0]+w**2*basis[1], *basis[5:8]]
    else:
        def unpack(v):
            s, x, y, z = v[:4]
            centered = vector([(x+y+z)/2, (x-y-z)/2, (-x+y-z)/2, (-x-y+z)/2])
            a = centered + vector([s/4]*4)
            b = vector([*v[4:7], -sum(v[4:7])])-centered
            c = vector([*v[7:10], -sum(v[7:10])])-centered
            return a, b, c

        im = K(5)
        assert im**2 == -1
        X = [basis[0]+basis[1], basis[2]+im*basis[3], *basis[4:7]]
        Y = [basis[0]-basis[1], basis[2]-im*basis[3], *basis[7:10]]

    def quadratic(v):
        a, b, c = unpack(v)
        return sum(a)**2+a*b+a*c+b*c

    def cubic(v):
        a, b, c = unpack(v)
        return sum((2*x-sum(a))*y*z for x, y, z in zip(a, b, c))

    def polar(v, w):
        return quadratic(v+w)-quadratic(v)-quadratic(w)

    X, Y = matrix(K, X), matrix(K, Y)
    cross = matrix(K, n, n, lambda i, j: polar(X[i], Y[j]))
    Y = cross.inverse().transpose()*Y
    assert all(polar(v, w) == 0 for family in (X, Y) for v in family for w in family)
    assert matrix(K, n, n, lambda i, j: polar(X[i], Y[j])) == matrix.identity(K, n)
    pairs = list(combinations(range(n), 2))
    ring = PolynomialRing(K, names=[f"s{i}{j}" for i, j in pairs], order="degrevlex")
    skew = matrix(ring, n, n)
    for (i, j), var in zip(pairs, ring.gens()):
        skew[i,j], skew[j,i] = var, -var
    for flip in product((False, True), repeat=n):
        left = matrix(ring, [Y[i] if flag else X[i] for i, flag in enumerate(flip)])
        right = matrix(ring, [X[i] if flag else Y[i] for i, flag in enumerate(flip)])
        plane = left + skew*right
        equations = [cubic(v) for v in plane]
        for i, j in pairs:
            equations.extend([cubic(plane[i]+plane[j]), cubic(plane[i]-plane[j])])
        for i, j, k in combinations(range(n), 3):
            equations.append(cubic(plane[i]+plane[j]+plane[k]))
        assert list(ring.ideal(equations).groebner_basis(algorithm="libsingular:slimgb")) == [ring.one()]
    print(f"All {2**n} charts have unit ideal (dimension {n} planes).")


if __name__ == "__main__":
    reduced_case(True)
    reduced_case(False)
