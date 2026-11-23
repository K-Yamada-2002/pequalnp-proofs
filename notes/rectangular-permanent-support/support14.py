"""Exact certificates for the two remaining 14-cell supports in L-gct-179."""
from itertools import combinations_with_replacement, permutations, product
from math import prod
from sage.all import QQ, CyclotomicField, PolynomialRing, matrix, vector
from support_bound import quadratic_data


def polynomial(rows):
    cells, quadratic = quadratic_data(rows)
    ring = PolynomialRing(QQ, names=[f"x{i}" for i in range(len(cells)-1)])
    entries = dict(zip(cells, [*ring.gens(), -sum(ring.gens())]))
    level = sum(prod(1+entries.get((i, j), 0) for i, j in enumerate(p))
                for p in permutations(range(5), 4)) - 120
    return quadratic, level


def first_pattern():
    Q, F = polynomial((1, 15, 15, 31))
    xs = F.parent().gens()
    grad = [F.derivative(x) for x in xs]
    hess = [[g.derivative(x) for x in xs] for g in grad]
    zero = vector(QQ, len(xs))

    def tangent(points):
        return matrix(QQ, [[g(*p) for g in grad] for p in points]).right_kernel().basis_matrix()

    def form(V, p):
        return V * matrix(QQ, [[g(*p) for g in r] for r in hess]) * V.transpose()

    def quotient(V, H, G):
        assert H.right_kernel().is_subspace(G.right_kernel())
        ix = H.pivots()
        B, C = (m.matrix_from_rows_and_columns(ix, ix) for m in (H, G))
        assert B.is_invertible()
        return V.matrix_from_rows(ix), B, C

    assert Q.rank() == 12 and form(matrix.identity(QQ, 13), zero) == 6*Q
    r, = Q.right_kernel().basis()
    V = tangent([zero, r, 2*r])
    H = form(V, zero)
    assert (V.nrows(), H.rank()) == (12, 10)
    K = H.right_kernel().basis_matrix()*V
    P, B, C = quotient(V, H, form(V, K[0]+2*K[1]))
    ev = QQ(1)/3
    E = (C-ev*B).right_kernel().basis_matrix()
    assert dict((B.inverse()*C).charpoly().roots())[ev] == 2 and E.nrows() == 1
    K = K.stack(E*P).row_space().basis_matrix()
    assert K.nrows() == 3
    points = [zero]+[sum(t) for d in range(1, 4) for t in combinations_with_replacement(K.rows(), d)]
    V = tangent(points)
    H = form(V, zero)
    assert V.nrows() == 11 and H.rank() == 8 and (H.right_kernel().basis_matrix()*V).row_space() == K.row_space()
    G = sum((i+1)*form(V, p) for i, p in enumerate([zero, *K.rows()]))
    P, B, C = quotient(V, H, G)
    roots = (B.inverse()*C).charpoly().roots()
    assert len(roots) == 4 and all(m == 2 for _, m in roots)
    field = CyclotomicField(3)
    t = PolynomialRing(field, "t").gen()
    choices = []
    for ev, _ in roots:
        E = (C-ev*B).right_kernel().basis_matrix()
        assert E.nrows() == 2
        M = E*B*E.transpose()
        f = M[0, 0]+2*t*M[0, 1]+t*t*M[1, 1]
        lines = [(E[0]+u*E[1])*P for u, _ in f.roots()]
        if M[1, 1] == 0:
            lines.append(E[1]*P)
        assert M.rank() == 2 and len(lines) == 2
        choices.append(lines)
    count = 0
    for directions in product(*choices):
        candidate = K.change_ring(field).stack(matrix(field, directions))
        assert candidate.rank() == 7
        test = sum((i+1)*v for i, v in enumerate(candidate.rows()))
        assert F(*test) != 0
        count += 1
    assert count == 16
    print("First support: all 16 candidate planes excluded over Q(zeta_3).")


def second_pattern():
    Q, F = polynomial((7, 7, 7, 31))
    assert Q.rank() == 12
    xs = F.parent().gens()
    # The last omitted coordinate is minus the sum of the other 13.
    A = matrix(3, 3, xs[:9])
    t = -sum(xs[:12])
    perm = sum(prod(A[i, j] for i, j in enumerate(p)) for p in permutations(range(3)))
    assert F.homogeneous_components()[4] == t*perm
    _, restricted = quadratic_data((7, 7, 7, 7))
    assert restricted.rank() == 11
    field = CyclotomicField(3)
    w = field.gen()
    ring = PolynomialRing(field, names="z0,z1,z2,u0,u1,u2")
    z, u = ring.gens()[:3], ring.gens()[3:]
    A = matrix(ring, 3, 3, lambda i, j: z[j]*w**i + u[j]*w**(-i))
    perm = sum(prod(A[i, j] for i, j in enumerate(p)) for p in permutations(range(3)))
    assert perm == 6*(prod(z)+prod(u))
    D = matrix(QQ, 3, 3, lambda i, j: int(i == j)-1)
    v = vector(ring, z)
    assert sum(a*a for a in A.list())-sum(sum(r)**2 for r in A.rows()) == 6*(v*D*vector(ring, u))
    assert D.det() != 0 and all(m != 0 for m in D.minors(2))
    print("Second support: quartic factor, rank 11 slice, Fourier cubic and all pairing minors verified.")


if __name__ == "__main__":
    first_pattern()
    second_pattern()
