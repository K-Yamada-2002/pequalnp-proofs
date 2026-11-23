"""Check both moment identities coefficient by coefficient, using all 120 permutations."""
from itertools import permutations
from sage.all import QQ, identity_matrix, matrix


def verify():
    cells = [(i, j) for i in range(5) for j in range(5)]
    matchings = matrix(QQ, [[int(p[i] == j) for i, j in cells]
                            for p in permutations(range(5))])
    assert list(sum(matchings.rows())) == [24] * 25
    # Off the diagonal, the Gram matrix counts two prescribed entries in a matching.
    hessian = matchings.transpose() * matchings - 24 * identity_matrix(QQ, 25)
    assert hessian == matrix(QQ, 25, 25, lambda k, l: 6 * (
        1 - int(cells[k][0] == cells[l][0]) - int(cells[k][1] == cells[l][1])
        + int(k == l)))
    print("Verified 25 first derivatives and 625 second derivatives at J.")


if __name__ == "__main__":
    verify()
