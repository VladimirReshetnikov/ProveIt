# The nested BB profile (1,7,0)

This is a finite exact certificate for the unit-left-population BB derivative
with forced core masks (1,7), empty unforced core column, and arbitrary
right activities. It uses the same fifteen projected-pair charts and
private-mask-4 restoration as profile_130_proof.md.

Keep its definitions n,b,m,z,p,q,h,k, with m=n+b. In particular,
h=zm-z(z+1)/2 and k=nz-tau(tau+1)/2, tau=N5+N7. Thus p>=1,n>=1,b>=0.
For a column mask S, let d(S)=|S|, H(U,V) count matchable two-row supports,
and C(U,V,W) count matchable three-row supports.

## Exact aggregate matrix

Boolean endpoint counting gives

E=p+3n+b+2, x=q+h+2k+2z,
r_S=p d(S)+n H(7,S)+b H(1,S)+C(1,7,S),
v_S=q d(S)+k H(7,S)+(h-k)H(1,S)+z C(1,7,S),
B_ST=p H(S,T)+n C(7,S,T)+b C(1,S,T).

The full seven-class matrix has R=3rr^T/(4E)-B,
w=3xr/(4E)-v, scalar entry c=3x^2/(4E). Its Schur scalar is

S=c-w^T R^(-1)w = 2F/(p Psi),

where F is a quadratic polynomial in (q,h,k,z) with polynomial
coefficients in (n,b,p), and

Psi=4b^2n^2+16b^2np+2b^2p^2+12bn^3+45bn^2p+8bn^2
 +27bnp^2+20bnp+4bp^3-8bp^2+24n^3p+26n^2p^2+16n^2p
 +11np^3-8np^2+2p^4-8p^3-12p^2.

For a concise, unambiguous specification, the ten coefficients of F are
listed in aggregate_170.json, together with its expanded expression.
Equivalently F is the polynomial obtained from the displayed seven-class
matrix by (p Psi/2)(c-w^T R^(-1)w). The reader checker
check_170_schur.py constructs the matrix independently using injective
assignments and verifies all ten quadratic coefficients by a fraction-free
inverse. It imports no cached matrix or primary producer routine.

The denominator is strictly positive on the claimed domain: under
n=1+U,p=1+V,b=B the polynomial Psi has exactly thirty nonzero coefficients,
all positive, with constant 51. denominator_170.json contains the exact
rational coefficient list; check_170_schur.py verifies these signs directly.

## Reduced target and exact nonnegative decomposition

Substitute the exact population support polynomials for (n,b,p,q,h,k,z).
Then P=576F is an integer polynomial of degree thirteen with 19,888
nonzero terms. Its canonical coefficient list is reduced_170_target.json.
The original primary primitive Schur numerator is exactly

4n(bn+bp+2np+p^2) P.

The factor is strictly positive for p,n>=1,b>=0. This linkage is checked
coefficient by coefficient by make_reduced_target_fast.py; it is additional
verification, not an assumption needed for the fresh matrix reconstruction.

For each of the fifteen pair bases B, the certificate gives an exact
identity

P(B+X)=12(ph-mq)(B+X) M_B(X)+R_B(X),

where all coefficients of M_B and R_B are nonnegative. There are 277
nonzero rational multiplier terms and 317,512 nonnegative remainder
coefficients in total. The shared real-cone SOS from the (1,3,0) proof
certifies ph-mq>=0 throughout every such real chart. Therefore P>=0.

The primary optimizer only proposes multiplier coefficients; exact rational
reconstruction verifies the final identities. The separate reader replay
replay_reduced_certificates.py independently builds the support polynomials
by Boolean assignment existence and ascending unit translations. It uses
neither an optimizer nor the producer's polynomial routines. It reconstructs
P from F and checks every remainder coefficient and canonical hash.

The positive R-block on each open chart follows from the already proved
inertia argument and deleted-column degree-five marginal. Since S>=0, the
full class matrix is positive semidefinite there. Continuity of the original
matrix, with E>=1, includes chart boundaries. Every actual projected-rank-two
population contains one of the fifteen pair bases. Finally restore all
private mask-4 vertices using the private-leaf extension lemma at actual
populations. This proves the BB assertion for (1,7,0).

## Standalone replay

From this directory run: python -O run_checks.py

This runs both fresh matrix reconstructions and both exact certificate
replays. The matrix stage uses SymPy; the Boolean population and rational
identity stage uses only the Python standard library. No primary BB files
or optimization libraries are required by this reader entry point.
