"""Build the translated forms and verify the polynomial on the centered block."""
from itertools import permutations
from math import prod
from sage.all import QQ, CyclotomicField, PolynomialRing, matrix, vector
from support19 import quadratic_data


def data(rows):
    cells, Q = quadratic_data(rows)
    n = len(cells) - 1
    ring = PolynomialRing(QQ, names=[f"x{i}" for i in range(n)])
    xs = ring.gens()
    entries = dict(zip(cells, [*xs, -sum(xs)]))
    F = sum(prod(1+entries.get((i,j),0) for i,j in enumerate(cols))
            for cols in permutations(range(5))) - 120
    grad = [F.derivative(x) for x in xs]
    hess = [[g.derivative(x) for x in xs] for g in grad]
    def at(w):
        return matrix(QQ, [[h(*w) for h in row] for row in hess])
    zero = vector(QQ,n)
    assert at(zero) == 6*Q
    r, = Q.right_kernel().basis()
    points = [i*r for i in range(3)]
    V = matrix(QQ, [[g(*w) for g in grad] for w in points]).right_kernel().basis_matrix()
    forms = [V*at(w)*V.transpose() for w in points]
    return cells, V, forms, at


def centered_cubic():
    field = CyclotomicField(3)
    w = field.gen()
    R = PolynomialRing(field, names="a,b,c,d,z")
    a,b,c,d,z = R.gens()
    entries = {(i,j): a*w**(i+j) + b*w**(i-j) + c*w**(-i+j) + d*w**(-i-j)
               for i in range(3) for j in range(3)}
    f = sum(prod(1+z*entries.get((i,j),0) for i,j in enumerate(cols))
            for cols in permutations(range(5))) - 120
    assert f == 54*z**2*(a*d+b*c) + 12*z**3*(a**3+b**3+c**3+d**3)
    print("centered block: quadratic and cubic identities verified")
