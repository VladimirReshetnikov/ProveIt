# A squared transport coordinate with inverse Lucas correction

Research contribution for Vladimir Reshetnikov, 25 October 2026.

## Result and exact boundary

This component gives two ordinary polynomials in ten **strictly positive**
integer variables, each of exact degree 232 and 85 live binary arithmetic
operations. The squared-coordinate version reduces the degree of its
carrier numerator from 57 to 21. Its complete polynomial still has degree
232 because a different summand remains dominant.

The bV version combines the trace reduction in pinned package 163 with the
inverse correction in pinned package 164. A later repository check found
the identical 85-gate bV polynomial in the incoming Pooled Powers Separated
Radicals archive. It is therefore retained as a reproduced baseline, not
claimed as a new polynomial or a new complexity point. The b² version
settles the explicit open transport question in Section 9 of package 163.
It does so by changing the sign argument: the correction is evaluated at
the positive Pell coordinate k, so adverse negative-rank branches disappear.

The elementary bounds and congruences below compose with the specifically
identified native/refutation calibration in the retained parent proofs.
Thus, in ordinary ZFC, each equation has a positive solution if and only if
there is a finite syntactic ZFC refutation. Negation gives the requested
equivalence with Con(ZFC). This component does not supply a new end-to-end
Lean/Rocq closure, prove consistency, or establish a global minimality or
literature-priority claim. Its compact route retains K215/native ancestry.

The comparison snapshot is ProveIt commit
35fa5f6bc659e83f2b2034126c4bcf8e023fbe1c. The complete finite coefficient
recipe and exact numerical payloads are included; no coefficient is an
unspecified machine index or an unevaluated existential choice.

The additional late comparison is commit
0d75e561a8cefc8c30fc4224605a8984c810ad1c. `LATE_COMPARISON.json` records
the exact archive identities, identical bV rows and fixed coefficient
values, and the single changed b² gate. The inspected new compact proof
uses L=bV throughout; the b² carrier refinement remains distinct in that
checked material. It does not improve the total degree or gate count.

## 1. Complete formula

The independently quantified variables are

    J,F,alpha,i,T,w,s,n,eta,zeta > 0.

The fixed ports beta,K0,MC,MF are the whole directly indexed BFS943/radix67
tuple. They satisfy beta>=31 odd, K0>0, and 0<MC<beta<MF<2beta. Their
largest bit length is 592884. These inequalities alone do not calibrate
arbitrary replacement tuples: the actual four supplied integers are used.

Set, using polynomial abbreviations only,

    h=beta J, q=h+1, C=q-F-alpha,
    X=qw, Y=qs, k=eta+zeta, c=kY+eta,
    A=Y(X+1)+1, Delta=A²-1, H=4A-5,
    v=XY², ell=vk, E=1+ell(ell+k),
    R=[h(q-F)+alpha](q²-1)+(MC+q MF)J,
    B=(K0+w)C-F,
    U=ic², a=Delta U²E, F0=1+a, G=EF0,
    f=1+2a, Q=4Delta aF0,
    b=cT-R, V=fb-c, K=X(3c-2X)+2,
    e6=6(k-R-1)-ell(k²-4), D6=6q⁶,
    M=h D6 H,
    Z=h D6 [H(n-LB)+K]-H[D6 B+h(e6-6q⁴s)],
    P=Q(Z²-M²GV²)+(M²G-Z²).

The principal new weight is L=b². A companion uses L=bV.
The equation is P=0. All named registers are abbreviations, not additional
unknowns. The literal DAG contains only integer constants, addition,
subtraction and multiplication. It computes ell as (XY)(kY), reusing an
existing product, and f as a+F0. This avoids computing v as a separate node.

For the proof, not the defining polynomial, put

    e*=e6/6, rho=e*/q⁶, sigma=s/q²,
    t=B/h, kappa=K/H, W=1+hL, z=Z/M.

These quantities are not initially assumed integral. The exact rational
carrier identity is

    z=n+kappa+sigma-Wt-rho.                         (1)

## 2. Inherited root and index facts used before sign recovery

The root extraction in trace_proof.md, Sections 3--4, depends on the
definitions through Q,V,G, the fact that z=Z/M is rational, and the final
norm equation. It does not depend on the carrier weight L or on the
definition of the error e6. Therefore it applies unchanged to both new
graphs. Specifically, at every positive zero it proves

    E=tau², F0=f0², G=g², g=tau f0>0,
    z=epsilon g y, epsilon in {1,-1}, y a positive integer,
    QV²-(Q-1)y²=1,
    c=psi_A(p), p>=5 odd,
    k=2psi_(1+2v)(m), m>=2,
    k>=8v+4, c>8XY³>=8q⁴, c>X, K>0.

Here psi_A(0)=0, psi_A(1)=1 and
psi_A(j+2)=2A psi_A(j+1)-psi_A(j).

The exact trace identities are

    f²=1+4aF0, Q=Delta(f²-1)=4Delta²U²G,
    f-1=2Delta i²c⁴E.

They give f=1 modulo c and the same two residues V=-c modulo f and
V=-R modulo c as in the trace parent. The second residue does not yet
authenticate R; its use comes after recovering C>0.

The parent excludes auxiliary Pell indices one and three without any sign
assumption on R or B. For index three it derives

    f(b-4Delta f)=c-(4Delta+3), or
    f(b+4Delta f)=c+(4Delta+3).

Since c>4Delta+3 and f>2c, neither right side can be a nonzero multiple of
f. Consequently the auxiliary index is at least five. In particular,

    b != 0, sign(V)=sign(b),
    |b|>8f³-1/2,  g<f/2,  y<(3/2)|V|,  c<f/2.   (2)

These facts precede the sign recovery below. There is no circular appeal
to C>0 or R>0 in their use.

## 3. The new squared-coordinate transport lemma

At a zero, b is a nonzero integer. From V=fb-c and (2),

    |V| <= f|b|+c < (3/2)f|b|.

Therefore

    gy < (9/8)f²|b| < b²/2.                       (3)

For the second strict inequality, f>=1 and
8f³-1/2>(9/4)f² suffice, together with (2). Also b²>|b|, because (2)
implies |b|>1. Thus L=b² obeys exactly the two transport bounds needed:

    L>0, gy<L/2, |b|/q⁶<L/2.                     (4)

For the companion L=bV the same statements are already proved in the
trace parent, Section 4.

The key point is now the direction of the inverse correction. Since k>=2,

    vk(k²-4)/6 >= 0,
    e*=k-R-1-vk(k²-4)/6 <= k-R-1 < b,

where b-(k-R-1)=cT-k+1>0. This holds for every integer R, including
arbitrarily negative R. Hence rho<|b|/q⁶.

Suppose B<=-1. Then Wt=(1+hL)B/h<-L. In (1), n,kappa,sigma are positive,
and z=epsilon gy. Thus

    n=epsilon gy-kappa-sigma+Wt+rho
      < L/2-L+|b|/q⁶ < 0,

contradicting n>0. We have proved B>=0. Because F>0 and K0+w>0, the
definition of B now forces C>0.

This is the missing step for the b² question in package 163: its forward
correction could grow with a negative rank R, whereas the present inverse
correction has the correct sign independently of R. Merely substituting
b² into the forward-correction polynomial was not proved there and is not
asserted here.

## 4. Rank authentication and denominator recovery

After C>0, the unchanged fixed-mask estimate gives 3q<R<q⁴-2. With c>8q⁴
one has b,V>0. The normalized strong-index lemma and the signed auxiliary
index theorem in trace_proof.md apply with the same residues, so p=R.
In particular R is positive odd, q even and J odd.

All of the inverse-correction argument in inverse_lucas_proof.md,
Sections 3--4, now applies because its only carrier assumptions are (1),
integral z, and W=1 modulo h. For clarity its acyclic order is repeated.

The recurrence identity gives

    k=2m+8v C_m+32v² Z_m,
    C_m=binom(m+1,3), Z_m a nonnegative integer.

The even integer k makes k(k²-4)/6 integral, hence e* integral. Clearing
(1) gives q⁶|(e*-q⁴s), so q⁴|e*. Put t0=2m,
d=2m-R-1, A_m=C_m+4vZ_m and S_m=k²+k t0+t0²-4. The exact identity is

    3(e*-d)=4v²[24Z_m-A_m S_m].                   (5)

Since v=q³ws², q⁶ divides its right side. At a prime l|q with exponent
a_l>=1, this implies

    ord_l(e*-d)>=6a_l-ord_l(3)>=4a_l.

Hence q⁴|d. Monotonicity of the Pell recurrence gives 1<=m<R, and
therefore |d|<R<q⁴. It follows that m=(R+1)/2.

Do not yet claim q⁶|e*: the factor 3 in (5) cannot be canceled before
the radix has been proved dyadic. Instead integral z gives H|6hK. The
inherited uniform ratio bound and the exact whole-product projection give

    H | 6h(X-2^R)(2^R X+1),
    6h |(X-2^R)(2^R X+1)| < H.

Thus X=2^R, so q|X implies q is a power of two. Now (5) legitimately
gives q⁶|e*, hence rho integral. Projection also gives integral positive
kappa. Applying (1) modulo q² then gives q²|s, and applying it modulo h
gives h|B. This establishes the exact inherited native outer endpoint

    X=2^R, q³|Y, C>0, t=B/h>=0 integral,
    (K0+w)C-F=t(q-1).

The fixed-minus parity and native reconstruction interfaces in the retained
parents then produce a finite syntactic ZFC refutation. They use the whole
actual coefficient tuple, not just its scalar bounds.

## 5. Positive completeness, including the inverse error

A finite syntactic refutation gives the same canonical outer witnesses as
the retained native calibration: q a power of two, R=3 modulo 4,
X=2^R=qw, q³|Y and t=B/h>=0 integral. Set s=Y/q and construct the two
Pell sequences as in inverse_lucas_proof.md, Section 5. Their exact ratio
bound supplies eta,zeta>0.

Choose a positive period seed of the Pell matrix modulo c²tau, giving
the same i,f,I,g as in the parent. The trace parent's constructive
completeness supplies positive V,y and

    T=(V+c+Rf)/(cf)>0 integral.

This is the actual input T. Its existence is not inferred from an arbitrary
integer shift of a positive coordinate. Both b and V are then positive.

The inverse error rho may be negative. The inherited explicit estimates
are independent of the transport weight and of the use of f rather than f²:

    |rho| < vk³/3,
    g > sqrt(Delta)c²E > c²v²k² > vk³,
    kappa+sigma < g/2.

Thus g>kappa+sigma+|rho|. For either L=b² or L=bV define

    n=gy+(1+hL)t+rho-kappa-sigma.

Every term is integral, y>=1, t>=0 and the preceding strict inequality
makes n>0. Equation (1) now has z=gy, so P=0. Every independent input is
strictly positive. Soundness and completeness have both been proved.

## 6. Exact degree and finite checks

Write q0=beta J, k0=eta+zeta and

    B0=k0 s T-q0²(q0-F).

The whole highest homogeneous component of either polynomial is

    -9*2^10 q0^100 w^26 s^58 i^10 k0^32 B0².       (6)

It is nonzero for the actual beta>0, so the degree is exactly 232.
For the b² version the degrees of Q,M,G,V,Z are 80,11,50,40,21.
Thus QZ² has degree 122, while -Q M² G V² has degree 232 and is the
unique dominant summand. For bV, Z has degree 57 and QZ² degree 194;
the same other summand remains dominant. Reducing the degree of Z is a
structural improvement, not a further reduction of total degree.

The exact finite verifier checks every live gate through 36 free-polynomial
cuts per graph, the full homogeneous component (202 expanded monomials),
the exact parent/child gate edit, all coefficient bytes and 22 deliberate
operator corruptions per graph. The builder reconstructs the four constants
from the printed finite recipe and matches their pinned raw SHA-256 hashes.
These computations authenticate polynomial artifacts; they neither test
consistency nor replace the unbounded mathematical arguments above.

## 7. Source attribution and retained proof boundary

The frozen source paths, all at the comparison commit, are:

- con-zfc-diophantine-forms/163-trace-radical/compact/PROOF.md;
- con-zfc-diophantine-forms/163-trace-radical/compact/equations/trace87_degree232.json;
- con-zfc-diophantine-forms/163-trace-radical/compact/coefficient_recipe.tex;
- con-zfc-diophantine-forms/164-unsquared-factors-linear-selectors/positive/PROOF.md;
- con-zfc-diophantine-forms/149-cofinal-witnesses-centered-carriers/positive/rebuild_coefficients.py.

All are under Computability/DiophantineConsistency in VladimirReshetnikov/ProveIt.
The sparse polynomial helper and finite checker are adapted with attribution
from package 163. Its retained parent proofs name the underlying all-index
Pell, uniform-ratio, indexed-native and refutation interfaces. The current
repository deduplicates much of their transitive closure; this component
retains those source references and does not claim to ship or rebuild the
entire formal closure.
