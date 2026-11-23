# Tests for seven-dimensional level spaces on fifteen positions

Here the target is the same rectangular permanent as in [the 14-position result](README.md).
There are 27 support orbits on fifteen positions. Each original total-sum-zero hyperplane
has dimension 14. The characteristic-zero Hessian is nondegenerate in all 27 cases.
The following tests address particular orbits.

## Reduction for a distinguished row

Let $s$ be the number of supported entries of this row. The space $R$ of variations in just
this row with row sum zero is isotropic of dimension $s-1$. The polar form of the quadratic
term, applied to a variation in $R$, shows that $R^\perp$ consists of the matrices whose
column sums *on the other rows* agree across the $s$ columns of the distinguished row.
These are precisely the constraints used in [lift15.py](lift15.py). A point of
$R^\perp/R$ is represented by these other rows; the sum in the distinguished row is
already determined. The last supported position of that row may absorb its entire sum.

A seven-dimensional isotropic subspace $L$ is equal to $L^\perp$ when the ambient form is
nondegenerate. Set $h=\dim(L\cap R)$. The pairing of $R$ with $L$ has rank $s-1-h$, so
the image of $L\cap R^\perp$ in $R^\perp/R$ has dimension $k=8-s$. This is half the
dimension of the nondegenerate quotient. A basis of the projected $k$-plane has some
choice of linear lifts to $L$. Thus the cubic and quartic matching sums must vanish on
at least one lifted plane. The scripts use unweighted sums over matchings of each size:
these differ from the Taylor coefficients by the nonzero factors $(5-d)!$ for $4\times5$.

## Why one prime suffices

If a complex seven-plane existed, the homogeneous coefficient equations on one affine
Grassmannian chart would have a solution over a number field by the Nullstellensatz.
Choose a prime above the tested rational prime $p>4$. Among the nonzero maximal minors of a basis matrix take one
of minimal valuation, and row-reduce its columns to the identity. Cramer's rule shows
that every entry is then integral at the chosen prime. Reducing entries preserves rank
seven, because this minor is now the identity. All homogeneous coefficient identities
are preserved, too. It therefore suffices to exclude a seven-plane over the *algebraic
closure* of the field with $p$ elements. The unused cells may specialize to zero.
We specialize the original seven-plane before choosing any quotient or lift. In the
distinguished-row calculation, the full rank of the matrix of the column-sum differences
and nondegeneracy of the quotient quadratic form ensure nondegeneracy of the original
form at the tested prime as well.

## Why the charts cover all possibilities

Use a hyperbolic basis in the quotient, in $k$ pairs. On a maximal isotropic $k$-plane,
the coordinate functionals from any $j$ pairs span dimension at least $j$: their common
kernel is isotropic in the nondegenerate $2(k-j)$-dimensional complementary space and
has dimension at most $k-j$. Thus one functional can be chosen from each pair so the
$k$ choices are independent (the linear independent-transversal theorem). For completeness,
if a proper nonempty subfamily achieves equality, first make independent choices there,
then pass to the quotient by their span and use induction on the remainder. If no such
subfamily exists, choose one nonzero functional from the first pair and quotient by it.
Every remaining nonempty subfamily had a spare dimension, so induction applies again.
On the resulting chart a plane is the row space of the identity alongside a skew-symmetric
matrix. All $2^k$ charts are tested. The free lifts in the distinguished row supply an
additional $k(s-1)$ scalar variables.

The cubic and quartic on a proposed lifted basis must vanish at sums of $d$ basis
vectors with repetition for $d=3,4$. Each chart calculation tests necessary evaluations;
a Gröbner basis consisting of 1 certifies inconsistency even over the algebraic closure.
A proper ideal in a chart does not by itself give a seven-plane.

## The two orbits with a singleton row

For masks $(1,15,31,31)$ and $(1,30,31,31)$, the quartic factors into the singleton entry
and the sum of the triple products in distinct columns on the other rows, excluding column
zero. If the singleton entry vanishes identically, three active rows remain. The checked
three-row bound [L156](https://github.com/brilliant-hq/pequalnp-proofs/blob/9fb57df/lean/PEqualNP/Gct/L156.lean) gives dimension at most six;
its proof works over the complex numbers. Otherwise the cubic factor vanishes identically.
Perform the isotropic reduction over the complex numbers on the distinguished *column*
zero instead. In the first case the three other row vectors $a,b,c$ on the last four
columns all have sum zero, and $a_3=0$. In the second case $b,c$ have sum zero and $a$
is unrestricted. In both cases the reduced quadratic form, up to nonzero scale, is
$(\sum a)^2+a\cdot b+a\cdot c+b\cdot c$. For the term $(\sum a)^2$ in the second
case use a representative with entry $-\sum a$ in the singleton row and zero in the
remaining positions of column zero. The cubic factor on the quotient is
$\sum_j (2a_j-\sum a)b_jc_j$, by inclusion-exclusion on the three columns.
Both forms are independent of the lifts.

The quotient would therefore contain a common isotropic plane of dimension four or
five, respectively. Specialize that plane by the minimal-minor argument above, *after*
the characteristic-zero reduction in this case. [singleton_row15.py](singleton_row15.py)
computes unit ideals over the field of 13 elements on all 16 and 32 charts. The other
support with an empty row, $(0,31,31,31)$, also follows directly from L156.

## Verified coverage

| Row masks | Reason | Charts |
|---|---|---|
| (0,31,31,31) | Three-row theorem L156 with five columns | — |
| (1,15,31,31) | Cubic after reduction along column zero, characteristic 13 | 16 |
| (1,30,31,31) | Cubic after reduction along column zero, characteristic 13 | 32 |
| (3,7,31,31) | Distinguished-row lift, characteristic 13 | 8 |
| (7,7,15,31) | Distinguished-row lift, characteristic 7 | 8 |

Reproduce the four chart calculations with the following commands.
```sh
sage -python singleton_row15.py
sage -python lift15.py --prime 13 3,7,31,31
sage -python lift15.py --prime 7 7,7,15,31
```

This list covers five of the 27 support orbits of size 15. The other 22 are unclassified by the results reported here.
