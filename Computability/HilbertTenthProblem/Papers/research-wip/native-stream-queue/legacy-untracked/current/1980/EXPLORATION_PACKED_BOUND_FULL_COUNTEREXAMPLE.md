# Deleting the packed bound makes every admissible index accept every positive input

This note strengthens the earlier coding-level exclusion in
`EXPLORATION_DROPPED_PACKED_BOUND.md`. For the 102-operation system
justified by `SINGLE_OFFSET_ENCODING_PROOF.md` and
`PELL_COMMON_WITNESS_PROOF.md`, it extends the unbounded family to
every retained positive Pell witness. The resulting statement is
universal: for every admissible fixed index and every positive queried
input x, simply deleting

    S2+alpha=q^2, S2=ell+eq

makes the remaining system have infinitely many positive solutions.
Thus every admissible index represents all positive integers after
this deletion, regardless of the set it originally represented. This
is an exclusion of that specific one-operation deletion, not a lower
bound on possible certificate complexity or on other replacements
for the bound. All assertions below concern the fixed 102-operation
system and its admissibility conditions; they do not quantify over
arbitrary, inadmissible triples of parameters.

## Fixed data for any admissible index and any positive input

Fix any admissible index (Z,V,H), with its coefficient polynomial
D(T), indicator polynomial ell_0(T), and coefficient code e_0(T)
from `SINGLE_OFFSET_ENCODING_PROOF.md`. Fix any positive queried
input x. Choose the code coordinates delta=1 and u=x^2, with all
other ordinary and dummy coordinates zero. The guard is satisfied;
no assumption is made about any other ordinary quadratic row.

Choose b a sufficiently large power of two and define the fixed
canonical quantities

    B=Hb^2, q=B^L, N=q^8,
    lambda=(q^2-1)/(B-1), theta=B-Z,
    e=e_0(B), ell_0=ell_0(B),
    Ccode=x+g=x+B+x^2*B^(v_59).

Specifically, take b>x^2, so every chosen coordinate is smaller
than b. The delta digit makes g positive, and beta=b-x is positive.

The support and index bounds give

    e<q, lambda>q, Ccode<B^K, Z*Ccode^2<qB,
    Omega=Zlambda-2e>0,
    S3=Blambda*q-Omega*Ccode^2>0.

These estimates use the bounds on the code coordinates, not the
vanishing of the ordinary residuals. Indeed Z<B and L>3K+2 give
Z*Ccode^2<B^(2K+1)<qB, while e<q and lambda>q imply Omega>0.
The displayed formula can be rewritten as

    S3=lambda(qB-Z*Ccode^2)+2e*Ccode^2>0.

The canonical packing still has all its ordinary numerical ranges
and a positive index R_0>=N. These numerical ranges do not assert
that its binary no-carry tests hold.

The positivity of the packed-congruence witness also needs no row
equations. Define the polynomial with nonnegative coefficients

    Pcode(T)=ell_0(T)+e_0(T)*T^L.

It is nonconstant, and B>Z, so Pcode(B)>Pcode(Z)=V. Polynomial
evaluation modulo B-Z shows that

    t_0=(Pcode(B)-Pcode(Z))/(B-Z)

is a positive integer. It satisfies

    ell_0+eq=V+t_0 theta.

For a general positive ell define the same arithmetic packing

    S(ell)=g+q^2(ell+eq+q^2S3),
    Tplus(ell)=q^2(1+theta*lambda)-(b-1)ell+(B-4)ell*q^4,
    R(ell)=S(ell)(N^2-N)+Tplus(ell)(N^2-1).

The coefficient of ell in R is the strictly positive integer

    K_R=q^2(N^2-N)+[(B-4)q^4-(b-1)](N^2-1).

In particular, R(ell_0)=R_0.

## The exact unbounded family

Choose a positive integer A_* for which

    P_*=theta*A_*K_R>R_0, D_*=P_*-R_0>0.

For each sufficiently large positive integer m, put

    ell_m=ell_0+theta*A_*(2^m-1),
    t_m=t_0+A_*(2^m-1),
    R_m=R(ell_m)=P_*2^m-D_*.

The packed congruence is exact, and Omega, S3 and all geometric
and power equations are unchanged. Both S(ell_m) and Tplus(ell_m)
are positive because their coefficients of ell are positive.
For large m the removed packed bound fails, while R_m>=N.
We may also require R_m>2N^3: the construction below does not
invoke the upper bound that the original packing would have given.

If 2^m>D_*, the binary digit sum satisfies the exact identity

    s_2(R_m)=s_2(P_*-1)+m-s_2(D_*-1).

Indeed the low m bits in

    R_m=(P_*-1)2^m+(2^m-D_*)

are the bitwise complement of D_*-1 in that width. Therefore the
factorial valuation identity

    v_2(binomial(2R_m,R_m))=s_2(R_m)

shows that `N^2` divides this central binomial coefficient whenever

    m>=2log_2(N)+s_2(D_*-1)-s_2(P_*-1).

Fix any such sufficiently large m and write R=R_m. There are
infinitely many choices of m, with distinct ell_m and R_m. We now
extend each choice to all the positive Pell witnesses. This final
step is what was not asserted in the earlier exclusion note.

## All remaining Pell equations have positive witnesses

Set

    J=2R+1, U=4^J, w=U/N^2,
    xi=(U+1)^(2R)/U^R,
    Y=floor(xi), s=Y/N^2,
    a0=Y(U+1), A=a0+4,
    Q=UY^2, P=2Q+1, D=UY.

The first quotient w is positive integral: N and U are powers of
two, and

    N^2<=R^2<=4^R<4^J=U.

The binomial expansion has integer part Y with

    0<xi-Y<2^(2R)/U<1/4,
    Y=binomial(2R,R) modulo U.

Since both U and the central binomial coefficient are divisible
by N^2, so is Y, and s is a positive integer. Also Y>=U^R.

Choose the exact Pell coordinates

    C=psi_A(J), d=chi_A(J), K=psi_P(R+1),
    tau=(chi_P(R+1)-1)/2,
    h=(K-R-1)/D.

The odd parameter P makes tau positive integral. The congruence
modulo P-1=2UY^2, together with strict Pell growth, makes h a
positive integer. They satisfy the shared first norm and index
equation exactly.

The ratio estimates do not require the failed upper bound R<2N^3
when these witnesses are selected explicitly. At the chosen indices,
the lower growth estimate of `PELL_UNIT_SCALE_PROOF.md` gives

    C/K >= xi*(1+7/(2a0))^(2R)*(1+1/(2Q))^(-R) > xi.

Here 14Q>a0 follows immediately from Q=UY^2, a0=Y(U+1),
and U,Y>=4096. For the upper estimate, Pell growth gives

    C/K < xi*(1+4/a0)^(2R).

The elementary binomial/geometric estimate applies because

    8R/a0<8R/U^(R+1)<1/2.

It gives C/K<xi*(1+16R/a0). Since xi<Y+1<2Y,
consequently

    0<C/K-xi<32R/(U+1)<1/2,

where the last inequality follows directly from U=4^(2R+1)>64R.
It follows that

    Y<xi<C/K<xi+1/2<Y+3/4.

Thus eta=C-KY and zeta=K-eta are positive integers, giving both
positive interval equations. The supplied variable a is a0.

Here is an explicit existence construction for the auxiliary norm;
it also avoids any hidden dependence on the failed packed range.
Consider the integer matrix

    M_A = [[A, A^2-1], [1, A]], det(M_A)=1.

Its reduction modulo C^2 belongs to the finite group
SL_2(Z/(C^2)Z). Thus some positive integer m_0 satisfies
M_A^(m_0)=I modulo C^2. The Pell matrix identity is

    M_A^m = [[chi_A(m), (A^2-1)psi_A(m)],
             [psi_A(m), chi_A(m)]].

Set

    f=chi_A(m_0), i=psi_A(m_0)/C^2.

Then f and i are positive integers, f>1, and

    f^2-(A^2-1)*(iC^2)^2=1.

Now put

    G=1+(A+1)(f^2-1),
    o=(chi_G(J)+d)/f, j=(psi_G(J)-J)/C.

The auxiliary norm implies G=1 modulo C, while the definition
gives G=-A modulo f. Since J is odd, the Pell polynomial
congruences give

    chi_G(J)=-chi_A(J)=-d modulo f,
    psi_G(J)=J modulo C.

Thus o and j are integers. The numerator defining o is positive,
and G>1 and J>=2 give psi_G(J)>J, so j is positive. The equation
of-d=chi_G(J), together with its Pell norm, supplies the signed
auxiliary equation exactly.
Choose

    kappa=psi_A(L), mu=chi_A(L),
    Delta=(kappa-L)/(A-1), phi=C-kappa.

The congruence psi_A(L)=L modulo A-1 makes Delta integral;
strict Pell growth makes Delta positive. Also 2<=L<J because
R>=N>=3L, so phi is positive. Both second Pell coordinates are
positive.

Both exponent relations have their intended values U=4^J and
q=B^L. The standard polynomial congruences therefore provide the
integer quotients

    gamma=[d-(A-4)C-U]/(8A-17),
    rho=[mu-(A-B)kappa-q]/(2AB-B^2-1).

They are positive because

    d-(A-4)C=4C-psi_A(J-1)>3C>U,
    mu-(A-B)kappa=B*kappa-psi_A(L-1)>(B-1)kappa>q.

For these comparisons, A>U^(R+1)>U^3 and A>q^3; the latter follows
from U>=N^2 and R>=N. The relevant moduli are positive since A>B
and A>4. The unchanged coding witnesses beta=b-x, sigma=S3 and
Omega are positive. If the unused alpha variable is retained after
its equation is deleted, assign it any positive integer.

All retained equations of the 102-operation system have now been
satisfied with positive unknowns. The index and queried input were
arbitrary, and the ordinary rows were never assumed to vanish.
Consequently deleting the packed bound makes every admissible index
accept every positive input, with infinitely many positive witness
tuples for each input.

In particular, the admissible indices include one representing the
empty recursively enumerable set: take the ordinary constant row
1=0 and pad by zero rows before the prescribed homogenization and
coefficient construction. Its homogeneous row is delta^2=0 and its
new coefficient target is 5delta^2. The construction above still
gives positive witnesses for every x, although that ordinary system
has no solution. This is a full false positive, including every
auxiliary Pell equation. A successful future reduction must replace
the packed bound by a constraint that excludes this family, or
change the representation more substantially.

## Finite regression, separate from the universal proof

`../verification/packed_bound_popcount_check.py` checks the exact
popcount family and factorial-valuation identity in 10,597 finite
cases, including 832 direct evaluations of central binomial
coefficients. It also checks 84,776 exact divisibility thresholds.
Its JSON receipt records PASS. These are finite arithmetic regressions;
the proof above, rather than those samples, establishes the statement
for every admissible index and every positive input and constructs
all positive Pell witnesses.
