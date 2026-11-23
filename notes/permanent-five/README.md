# Two restrictions on nine-dimensional spaces for the 5 by 5 permanent

Write $F(X)=\operatorname{per}(J+X)-120$, where $J$ is the all-ones matrix.
Assume $L$ is a complex linear space on which $F$ vanishes identically.
The following are partial results for L-gct-210. They use exact computations in Sage and linear algebra over the complex numbers.

## A support orbit on 19 positions

Of the 69 orbits of supports of size 19 under independent row and column permutations,
one has a degenerate Hessian on the total-sum-zero hyperplane. Its row masks are $(3,29,29,29,31)$, with the least significant bit indexing column zero. This orbit cannot contain a nine-dimensional example.

Suppose there were such an $L$ on this support. The Hessian at zero on the
18-dimensional hyperplane has rank 17. Its radical line must lie in $L$,
since the nondegenerate 17-dimensional quotient has isotropic dimension at most eight.
Take the echelon generator $r$ of this radical as in [boundary.py](boundary.py).
The three gradients at $0,r,2r$ cut out a 17-dimensional space $V$ containing $L$.
On $V$ the Hessian at zero has rank 16, so its radical line $K$ must also lie in $L$.
Both Hessians at $0,r$ descend to $V/K$ and vanish on $U=L/K$.
Write them as $B,C$ respectively. Since $B$ is nondegenerate and $U$ has dimension eight,
$U=U^{\perp_B}$ and $A=B^{-1}C$ preserves $U$.

The characteristic polynomial of $A$ is
$$
(x-10/9)^4(x-1)^4(x-25/27)^4(x-8/9)^4.
$$
The eigenspace $E$ for $25/27$ is exactly the image of the four-dimensional space of
centered matrices supported on rows 1,2,3 and columns 2,3,4 (zero-based).
The restriction of $B$ to $E$ has rank four. Its dimension exhausts the multiplicity,
so the projection onto $E$ along the other primary components is a polynomial in $A$.
Self-adjointness for $B$ identifies the other components with $E^{\perp_B}$.
The dimensions four and twelve give isotropic bounds two and six respectively.
Their sum is eight, so $U\cap E$ has dimension two. Since $K\subset L$,
the centered block itself contains a two-plane in $L$.

For $0\le i,j<3$, write its entries as
$$
 a\omega^{i+j}+b\omega^{i-j}+c\omega^{-i+j}+d\omega^{-i-j},
$$
where $\omega$ is a primitive cube root of unity. These four independent characters span all centered blocks. Expansion of the five-by-five permanent along this block gives the coefficients $54(ad+bc)$ and $12(a^3+b^3+c^3+d^3)$ in degrees two and three. Both must vanish identically. The first identity says that all matrices with rows $(a,b),(c,-d)$ have rank at most one. A linear two-plane of such matrices has a fixed left or right factor. Two independent rank-one generators with neither factor proportional would have a rank-two sum.

For a fixed left factor $(s,t)$ the cubic becomes $(s^3+t^3)u^3+(s^3-t^3)v^3$ with $u,v$ independent. Both coefficients can vanish only if $s=t=0$. The fixed right factor gives the same contradiction by transposition. This excludes the 400 labelled supports in this orbit and leaves 68 support orbits at size 19 unresolved.

Run `sage -python support19.py` for the orbit counts and `sage -python boundary19.py`
for the Hessian, spectral identification, and centered-block polynomial.

## A bound involving complex conjugation, with no support restriction

Let $M=L\cap\overline L$ for entrywise conjugation. Then $\dim_{\mathbb C} M\le 8$.
In particular the proposed dimension bound holds whenever $L$ is stable under conjugation.

Write $s(X)$ for the sum of the entries, $r_i(X)$ for row sums, and $c_j(X)$ for column sums.
The first derivative of $F$ at zero is $24s(X)$. Its Hessian divided by six is
$$
s(X)s(Y)-\sum_i r_i(X)r_i(Y)-\sum_j c_j(X)c_j(Y)+\sum_{ij}X_{ij}Y_{ij}.
$$
Indeed each entry belongs to 24 permutations, and two distinct entries in distinct rows
and columns occur together in six permutations. Since $F$ vanishes on $L$, its first derivative
annihilates $L$ and its Hessian vanishes on $L\times L$.

Map $M$ complex-linearly to eight coordinates by taking the first four row sums and
the first four column sums. For an element $X$ in the kernel all row and column sums
vanish, since $s(X)=0$. We have $\overline X\in L$ by the definition of $M$.
Applying the Hessian identity to $(X,\overline X)$ now gives $\sum_{ij}|X_{ij}|^2=0$,
hence $X=0$. Injectivity proves the bound. In the unrestricted complex problem a
nine-dimensional $L$ would have a nonzero centered direction, and the conjugate of
every such direction would have to lie outside $L$.

For arbitrary size $n\ge 2$, the same counting gives derivatives scaled by $(n-1)!$ and $(n-2)!$, respectively. Taking the first $n-1$ row sums and $n-1$ column sums in the injectivity argument proves $\dim_{\mathbb C}(L\cap\overline L)\le 2n-2$. For $n=1$ the level condition forces $L=0$. This proves a restricted case of L-gct-086.

Run `sage -python margins.py` to check the derivative tensors against the 120 permutations.
