# The nested BB profile (1,3,0)

This proof concerns unit left populations. The right variables remain arbitrary.
The two forced core columns have row neighborhoods {1} and {1,2}; the unforced
core column is empty. Remove the exterior left vertices of mask 4, restoring
them at the end by the private-leaf extension lemma.

Write the remaining class populations as N1,N2,N3,N5,N6,N7. Set

n=N1+N3+N5+N7, b=N2+N6, m=n+b, z=N5+N6+N7,
tau=N5+N7,
p=(N1+N5)(N2+N6)+(N1+N5)(N3+N7)
  +(N2+N6)(N3+N7)+binom(N3+N7,2),
h=zm-z(z+1)/2, k=nz-tau(tau+1)/2.

Here p counts L pairs matching the forced columns, h counts L pairs completed
to a basis by an extra generic mask-3 row, k counts those completed by a
mask-2 row, and q counts L bases on all three B columns. A genuine projected
pair basis gives p>=1 and n>=1. No rank-three L assumption is needed.

## Exact support and matrix identities

For column masks U,V,W, let H(U,V) and C(U,V,W) count matchable distinct
row supports of sizes two and three. Put d(S)=|S|. Boolean support counting,
including the overlap between the two possible core allocations, gives

E=p+2n+b+1, x=q+h+k+z,
r_S=p d(S)+n H(3,S)+b H(1,S)+C(1,3,S),
v_S=q d(S)+k H(3,S)+(h-k)H(1,S)+z C(1,3,S),
B_ST=p H(S,T)+n C(3,S,T)+b C(1,S,T).

The class Schur block is
R=3rr^T/(4E)-B, w=3xr/(4E)-v, c=3x^2/(4E).
The already proved deleted-column marginal controls R, including the class
correction and singular-population boundaries. On its nonsingular locus,
the remaining Schur scalar equals

S=c-w^T R^(-1) w = F/(p Gamma),
Gamma=4bn+bp+2n^2+2np+p^2-3p,
F=Gamma[2(q+h)(q+k)-k^2]
  -2[nh+bk-pz+(b+2n+p)q]^2.

The fresh checker check_130_schur.py constructs all supports by injective
assignments, forms the complete seven-by-seven R block, and verifies this
identity by a fraction-free inverse and all ten quadratic coefficients in
(q,h,k,z). It imports no cached matrix. The denominator is positive:

Gamma=(p^2-p)+(2n+b-2)p+2n^2+4bn>0.

## Exact positive-Rayleigh certificate

Let K=ph-mq. A rank-three Rayleigh inequality gives K>=0 at integer
populations. For the real-cone continuity argument we use a stronger,
explicit polynomial certificate instead. With
(A,B,C,U,V,W)=(N1,N2,N3,N5,N6,N7),

12K=6(BU-AV)^2+R0.

After each of the fifteen pair-basis translations N=e_i+e_j+X, X>=0,
all coefficients of R0 are nonnegative. The pairs are precisely the
unordered pairs of types in {1,2,3,5,6,7} that match both forced columns.
The standard-library checker verify_rayleigh_sos.py records 1,524
nonnegative remainder coefficients across those fifteen charts. Thus K is
nonnegative on the entire real chart, without treating a fractional
population as a graph.

After substitution of the population formulas, P=144F is an integer
polynomial of degree nine with 3,318 nonzero coefficients. For each pair
basis B the accompanying exact certificate gives

P(B+X)=12K(B+X) M_B(X)+R_B(X),

where every coefficient of M_B and R_B is nonnegative. There are 211
nonzero multiplier terms in total. The optimizer only proposes rational
multipliers; the recorded identity and all remainder signs are checked
exactly afterward. The coefficient files are reduced_130_target.json and
reduced_130_repair_i_j.json; reduced_130_repairs.json is the manifest.
No floating-point inequality is used in this conclusion.

The target is also linked exactly to the original cleared Schur numerator:
the latter's primitive polynomial is 4n(b+p)E times P. This independent
linkage is recorded in reduced_130_target.json. The factor is strictly
positive on the covered population domain.

Every actual projected-rank-two population contains one of these fifteen
pair bases. On each open real chart the previously proved R-block inertia
argument gives positive definiteness. The above certificate gives S>=0,
so the full class block is positive semidefinite. Passing to the boundary
is legitimate by continuity of the original matrix, with E>=1. Restore
all removed mask-4 vertices with the private-leaf extension lemma, applied
to actual populations. This proves the BB assertion for (1,3,0).
