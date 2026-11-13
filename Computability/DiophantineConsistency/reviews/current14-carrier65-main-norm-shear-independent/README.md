# Independent external review

The pinned maintained 65-row graph has positive `q`, `X`, `Y`, `E=XY`, and `a=E+Y`; with positive beta and positive inputs, `q>=2` and `m=EY>=2`. Its `Delta=a²+4a+3=(a+2)²−1` is strictly positive. The strong expression factors as `scaled_Ns=Delta*Ns`, where `Ns=f²−Delta*(i*c²)²`. Thus the zero equation is equivalent over the integers to `N0*N1*Na*Nt*Ns=1`.

For `L=a+2`, `N1=D²−(L²−1)c²` cannot be −1 modulo 4: if L is odd, L²−1 is 0 mod 4; if L is even, it is 3 mod 4 and the expression is a sum of two squares mod 4. N1 is independent of rank R in the pinned graph. At a zero of either the original expression or the expression with an acyclic replacement `R'=R+T*(N1−1)` in its other factors, N1 divides 1 and hence N1=1. Therefore R'=R at the zero and the two zero sets coincide coordinatewise. T denotes any integer-valued polynomial computed acyclically from the original inputs; this argument does not show either side has a zero.

The H=1 graph insertions occur after R and after N1, replace exactly the two downstream rank uses, and independently have 67 live arithmetic gates versus 65. The checker verifies the exact rank-change difference identity in a separate sparse polynomial implementation, all mod-4 residues and all source/output connections. This is external algebra, not a Lean/PDF theorem or a gate reduction.

## Additional Nt-anchor observation

The same graph also supports the originally proposed transport anchor, provided the coefficient is computed acyclically: `R'=R+T*(Nt−1)`, with Nt unchanged. The key first factor uses **multiplication**: `kY=k*Y`, `ell=E*kY`, and hence `N0=tau²−m(m+1)k²` with `m=EY>=2`. This is not the different expression `ell=E+kY`.

To see N0 cannot equal −1 even after an arbitrary integer rank change, suppose `x²−m(m+1)y²=−1` with y>0 minimal and take x>=0. Since m>=2, `my<x<(m+1)y`; write `x=my+r` with `0<r<y`. Rearranging gives `m(y²−2yr)=r²+1`, so `0<y−2r<y`. Multiplication by the norm-one unit `(2m+1)−2 sqrt(m(m+1))` gives another integer solution with second coordinate `y−2r`, contradicting minimality (replace its first coordinate by its absolute value if needed).

The other nontransport normalized factors also cannot be −1 modulo 4: N1 and Ns are square-minus-one discriminant forms, and `Na=(S V)²−(S²−1)y²` is another. Thus their product with Nt can be 1 only when Nt=1. Because Nt is rank-independent, the same argument holds both before and after the Nt-anchored shear, establishing coordinatewise zero equivalence. This observation is an independent external proof; it is not present as a new Lean theorem and gives no smaller circuit.
