# Nine more exclusions on fifteen positions

For the four-by-five rectangular permanent, write $J$ for the all-ones matrix. A level space is a complex linear subspace $L$ such that the sum of the 120 injection products in $J+X$ equals 120 for every $X$ in $L$. The following test excludes a seven-dimensional level space supported within each of nine sets of fifteen positions. Together with the [first five exclusions](fifteen.md), the results published here cover **14 of the 27** orbits under row and column permutations.

The nine orbits account for 7,560 labelled supports. Each row mask uses bit zero for the first column. For example, the first support below has rows of sizes two, three, five and five.

| Supported columns in each row, as bit masks | Certificate |
|---|---|
| (3,28,31,31), (3,15,23,31), (3,15,29,31) | Unit ideal over the rationals |
| (3,29,30,31), (7,7,27,31), (7,11,23,31) | Unit ideal over the rationals |
| (7,11,29,31), (7,15,25,31), (7,25,30,31) | Unit ideal over the rationals |

## A direction forced by a full row

On fifteen supported entries the linear Taylor term is 24 times the sum of the entries, so their sum vanishes on the level space. In the resulting fourteen-dimensional space $V$, let $F_d$ denote the sum of matching monomials of degree $d$. Its Taylor coefficient has the nonzero factor $(5-d)!$. In particular $F_2,F_3,F_4$ vanish on $L$. Let $B$ be the Hessian of $F_2$. The verifier checks its invertibility in the field used for each calculation. Since $L$ is isotropic and has dimension seven, its orthogonal complement for $B$ equals $L$.

Choose the first row whose mask is 31. The projection of $L$ onto that row cannot contain the vector of five ones. Otherwise subtracting a preimage from $J$ makes the entire row zero and forces the permanent to be zero. Thus there is a row functional annihilating the projection whose value on the ones vector is 1. Write its five coefficients as $(a_0,a_1,a_2,a_3,1-\sum_{i=0}^3a_i)$, extend by zero off the row, and restrict the resulting functional $\ell$ to $V$. The vector $z=B^{-1}\ell$ lies in $L^\perp=L$.

For every $z$ in $L$, the derivative of $F_d$ at $z$ annihilates $L$. Thus $u=B^{-1}dF_3(z)$ and $v=B^{-1}dF_4(z)$ also lie in $L$. This gives six equations in four parameters.

$$
 F_2(z)=F_3(z)=F_4(z)=F_2(u)=F_2(v)=F_2(u+v)=0 .
$$

For all nine supports, the Gröbner basis is $\{1\}$ over the rationals. The same tests also give unit ideals over finite fields, with characteristic seven for (7,11,23,31) and thirteen for the other eight.

## Reproduction

Run these commands in this directory with SageMath. The first computes the Gröbner bases over the rationals. A basis consisting of 1 gives a polynomial identity over the rationals, so the six equations have no common complex solution. The second repeats the calculation in the indicated finite characteristics.

```sh
sage -python row_normal15.py --rational
sage -python row_normal15.py
```

The [verifier](row_normal15.py) also expands the 120 injections to check the multiplicities of the matching monomials. It checks orbit representatives and multiplicities against the total of 15,504 labelled supports of size fifteen. The unrestricted existence question remains open in this work.
