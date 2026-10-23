# Support-aware quadratic coefficient extraction

## 1. Statement

Let `p_1,...,p_m` be integer polynomials of total degree at most two in
`n` variables. Let `A` be the union of their nonzero monomial supports,
as a subset of `Q={alpha in N^n: |alpha|<=2}`. Choose distinct positive
integer weights `w_1,...,w_n`, and write `e(alpha)=sum alpha_i*w_i`.
The required condition is

    alpha in A, beta in Q, e(alpha)=e(beta)  implies  alpha=beta.       (S)

It is NOT necessary that e be injective on all of Q. In particular,
monomials absent from every source polynomial may collide with each other.
Set `W=max_i w_i`, `s=2W+1`, and choose targets

    h_j=2W+(j-1)s, 1<=j<=m.

The targets may all be increased by the same nonnegative constant. Write
`p_j(X)=sum_alpha p_(j,alpha) X^alpha`, and define

    c_(j,alpha)=(2-|alpha|)! product_i(alpha_i!) p_(j,alpha),
    D(T)=sum_(j,alpha) c_(j,alpha) T^(h_j-e(alpha)),
    C_z(T)=(1+sum_i z_i T^w_i)^2.

All displayed exponents in D are nonnegative. Then, identically in the
integer indeterminates z,

    coefficient(T^h_j, C_z(T) D(T)) = 2 p_j(z),  1<=j<=m.            (E)

If `|c_(j,alpha)|<M`, every coefficient of D has absolute value less than M.
Every coefficient of `C_z D` has absolute value at most

    M (1+sum_i |z_i|)^2.                                           (B)

The coefficient bounds have no extra factor m.

## 2. Proof

The jth part of D is supported in `[h_j-2W,h_j]`. These intervals are
disjoint since consecutive targets differ by 2W+1. Within one row, (S)
makes the exponents of all supported monomials distinct. Thus every
nonzero coefficient of D is exactly one weighted source coefficient.

A monomial beta in C_z and a source monomial alpha in row k contribute to
target h_j precisely if

    h_j-h_k=e(beta)-e(alpha).

The right side belongs to `[-2W,2W]`, whereas a nonzero left side has
absolute value at least 2W+1. Therefore k=j. Condition (S), applied to
the supported alpha, gives beta=alpha. This use of (S) is the only
monomial-separation step; injectivity on absent monomials never enters.
The multinomial coefficient of beta in C_z is
`2!/((2-|beta|)! product beta_i!)`. Multiplication by c_(j,alpha)
cancels the denominator and gives `2 p_(j,alpha) z^alpha`. Summing gives (E).

For (B), replace z_i by |z_i| and bound the absolute value of each D
coefficient by M. A fixed coefficient of the convolution is bounded by M
times the sum of the nonnegative coefficients of
`(1+sum |z_i| T^w_i)^2`, which is `(1+sum |z_i|)^2`. Collisions between
absent monomials merely add coefficients of C_z and preserve that sum.

## 3. Concrete certificate

In the fixed variable order

    J,F,alpha,z,f,h,i,o,j,s,w,tau,eta,zeta,y,gamma,
    N,E,P,c,a,X,D,C2,L,F2,V,g,I,Baux,Delta,

the weight vector is

    10,14,128,112,178,157,173,145,129,63,123,84,151,75,2,124,
    3,169,31,190,185,184,189,177,90,111,19,30,68,51,144.

Adjoin weight zero to homogenize monomials to degree two. There are
`binomial(33,2)=528` pairs with repetition. The union of source supports
contains exactly 71 monomials. Every one of those 71 pair sums is unique
among all 528 pairs. The entire set has only 278 distinct pair sums,
so 250 repetitions are explicitly permitted. The vector is not a B2 set.
This both explains the reduction of W from 799 to 190 and certifies that
the construction uses the weaker hypothesis in a substantive way.

`code/verify_support.py` derives the exact supports from the literal parent
arithmetic circuits and checks every one of the 71,808 combinations of a
source term with an expansion monomial. The only 136 target hits are the
required diagonal hits. All 136 coefficients encoded in D occupy distinct
positions. The code performs finite integer equalities; the general proof
above supplies the unbounded statement for arbitrary witnesses.

## 4. The two inherited parents are distinguished

The ten-integer circuit specializes the 65-operation parent used by
package40. The nine-positive circuit specializes package31's 60-operation
parent used by package45. They use the same 31 variable names and identical
71-monomial support, but one transport coordinate is shifted. Specifically,
`z_old=z_new+1` changes the former residual system into the latter. The
verifier checks that identity symbolically, with all four coefficient ports
independent. It does not incorrectly identify their coefficients termwise.

`upstream/PARENT_TRANSPORT_SHIFT.md` gives the inherited positive-zero
bijection, including the non-algebraic step ensuring z_old>=2 on every
old positive zero. Both parent systems are therefore valid inputs to the
abstract transformation, but each final circuit retains its own exact rows.

The four native ports are the unchanged coherent tuple of package31:
`beta=B_native-1`, `K0=DC+B_native*DR`, `MC`, and the already shifted
`MF=MF_native+B_native-1`, with `B_native=2^1064921`. Their bit lengths are
1064921, 1070004, 1064921, 1064922. The complete finite coefficient recipe,
payloads, and source notices are included. Changing the additive weights
does not change these compiler constants.

## 5. Composition with the carry and finalizer interfaces

The parent variables are positive. The source rows are their polynomials
after the substitution `x_i=z_i+1`, with z_i nonnegative. The original fifth
row has value 1 at the zero vector. Move that row last; its factorial-weighted
constant coefficient is 2. Because every variable weight is positive, the
leading coefficient of D is 2 and the all-zero tuple is not a common zero.
For any radix B>M+1, summing the geometric series of possible negative
lower coefficients proves D(B)>0. This positivity argument is unchanged by
the support-aware hypothesis.

For the nine-variable source, use targets h_j=381j, so h_max=8382 and
K=h_max+2W=8762. The inherited coefficient bound is
`|c_(j,alpha)|<M=2^2134927`; take `b_floor=4096M=2^2134939`,
`b=b_floor+epsilon`, and `B=b^3`. Set

    ell=sum_i B^w_i, N0=B^191, N1=4 B^8763, N=N0*N1,
    mask=N0-1-(b-1)ell, targets=sum_j B^h_j,
    T=mask+(B-2)targets*N0,
    J=2(1+g)^2 D(B)+B sum_(k=0)^8762 B^k,
    S=g+J*N0,
    R=(N-1)[(S+T+1)N+T+1], Gcap=32b B^190.

The bounded branch `g<4b B^190` has `g<N0` and `0<J<N1`; also `0<T<N`.
These inequalities use only W, h_max, the coefficient bound, and the positive
leading term. For a power-of-two b, the no-carry condition with mask forces
`g=sum z_i B^w_i`, `0<=z_i<b`. Every coefficient of `C_z D` then has magnitude
less than `M(32b)^2<=B/4`. Adding B/2 to every coefficient gives strict digits
between zero and B. The mask `(B/2-1)sum B^h_j` forces each target digit to
be B/2, hence forces every source row to vanish by (E). Off-target collisions
cannot create carries because (B) already accounts for their full sum.

The inherited binary-popcount identity turns this no-carry assertion into
`N^2 | binomial(2R,R)`. Conversely, a common zero is encoded by choosing an
arbitrarily large power of two b above all its coordinates. The fifth-row
normalization ensures g>0. The same construction gives the stronger bound
`32g<Gcap` needed by Jones's ratio-completeness theorem. Thus the exact
source soundness/completeness contract used by package45 is preserved.

For the ten-integer source use targets h_j=380+381(j-1), h_max=8381,
K=8761, b=1+3f and B=2^2140030 b^2. All source formulas and inequalities
are exactly those of package40 after substituting W=190. Its coefficient
majorant `H=8(1+beta+K0+MC+MF)^2` satisfies
`2^2140030>4*33^2*H`. The factor cap=bB^190 retains the form required by
Sun's finalizer. In particular N=4B^8953 remains 1 modulo 3 on the relevant
square branch. The new (E) and (B) replace every use of full B2 uniqueness.

The finalizers and their variable domains are unchanged. Accordingly, with
the imported native compiler/K215 theorem, both completed fixed polynomials
have a zero in their declared domains exactly when ZFC has a finite syntactic
refutation. Classical negation gives the ZFC-provable consistency equivalence.
No consistency premise is used to prove that equivalence.

## 6. Exact degree and operation counts

The nine-positive polynomial uses 651 live binary arithmetic gates; the
nonnegative version uses 654. For W=190, `t=deg N=26862`. The cancellation-
resolved identity retained from package45 gives

    deg F9=1152t+12W+280=30,947,584,

with diagonal leading coefficient `2^2050`. The certificate circuit has
666 gates, but it evaluates exactly the same polynomial; the 651-gate
direct circuit is the deliverable used for operation comparison. The two
general polynomial identities connecting them are checked exactly over
integer polynomial rings in `code/audit_nine.py`. Modular leading-term
certificates are exact lower bounds, while modular replay of full formulas
is only an implementation diagnostic.

The ten-integer polynomial has 653 live arithmetic gates and exact degree
56,593,864. Independent total-degree propagation and a nonzero diagonal
leading coefficient modulo each of three primes certify equality of degree.
The circuit has 217 additions, 25 subtractions, and 411 multiplications.
Every fixed power is expanded into binary multiplication gates. Registers
are not extra variables; integer coefficient leaves are fixed inputs.

Compared with the wave6 sources, the ten-integer degree falls from
237,520,456 to 56,593,864, with 129 fewer gates. The nine-positive degree
falls from 129,875,980 to 30,947,584, with 137 fewer gates. These are concrete
improvements over the stated baseline, not proofs of globally optimal
degree, number of unknowns, or arithmetic complexity.

## 7. Remaining work

The new finite encoding can be formalized by making (S) an explicit finite
certificate consumed by a generic quadratic coefficient-extraction theorem.
The native-window/Pell compiler remains an inherited mathematical dependency;
these finite receipts do not remove that end-to-end formalization obligation.
The nine-variable route uses the formalized Jones ratio theorem and does not
depend on the separate ten-integer result of Sun. The latter is required only
for the unrestricted-integer deliverable.

Further improvements may exploit target-specific supports, allow overlapping
row intervals with a direct isolation certificate, or optimize label cost
jointly with multiplication chains. No optimality claim for W=190 is made.
