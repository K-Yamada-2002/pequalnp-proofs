"""Exclude the unique rank-17 orbit on 19 positions by its translated Hessian."""
from boundary import data, centered_cubic
from sage.all import QQ, matrix, vector


def exclude():
    rows = (3, 29, 29, 29, 31)
    cells, tangent, (hessian, translated, _), _ = data(rows)
    assert tangent.nrows() == 17 and hessian.rank() == 16
    radical = hessian.right_kernel().basis_matrix()
    assert radical * translated == 0
    pivots = hessian.pivots()
    B, C = (form.matrix_from_rows_and_columns(pivots, pivots)
            for form in (hessian, translated))
    operator = B.inverse() * C
    lifts = tangent.matrix_from_rows(pivots).stack(radical * tangent)
    # Four rectangular differences span the centered block in rows 1..3, columns 2..4.
    centered = []
    for i in (1, 2):
        for j in (2, 3):
            entries = {(i, j): 1, (i, 4): -1, (3, j): -1, (3, 4): 1}
            v = vector(QQ, [entries.get(pos, 0) for pos in cells[:-1]])
            centered.append(lifts.solve_left(v)[:16])
    E = matrix(QQ, centered)
    for eigenvalue, multiplicity in operator.charpoly().roots():
        eig = (C - eigenvalue * B).right_kernel()
        if E.row_space() == eig:
            assert multiplicity == eig.dimension() == (E * B * E.transpose()).rank() == 4
            print(rows, "characteristic polynomial:", operator.charpoly().factor())
            print("Centered block eigenvalue:", eigenvalue)
            return
    raise AssertionError("centered block did not form an isolated eigenspace")


if __name__ == "__main__":
    exclude()
    centered_cubic()
