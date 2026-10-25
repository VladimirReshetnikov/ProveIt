# Free auxiliary shifts and normalized product-square equations

Prepared for Vladimir Reshetnikov and ProveIt, with AI assistance.
Comparison snapshot: `1c5367452a0bd4dd7e9e4bceb1508b62dbd2ff61`.

## 1. Results and interpretation

This packet supplies three literal integer-coefficient polynomials in ten
strictly positive integer unknowns. Their zero-existence statements are
equivalent to a finite syntactic ZFC refutation under the whole indexed
BFS943 native calibration already accepted in the repository. Negating
this statement gives a ZFC-provable equivalence between unsolvability and
Con(ZFC). The new ordinary proofs below are arithmetizable in ZFC. They do
not supply a fresh end-to-end Lean/Rocq or encoded object-ZFC derivation.

| File | Unknowns | Binary operations | Exact degree |
|---|---:|---:|---:|
| `equation_83_436.json` | 10 positive | 83 | 436 |
| `equation_81_560.json` | 10 positive | 81 | 560 |
| `equation_80_750.json` | 10 positive | 80 | 750 |

The first strictly improves package 133's 84-operation, degree-436
equation by one operation, preserving domain and degree. The two normalized
equations are lower-operation/higher-degree alternatives. Package 133's
85/328 and the older 89/288 equations remain useful lower-degree choices.
No globally simplest equation or literature-wide novelty theorem is claimed.

The actual new steps are: (i) the squared transport weight permits deleting
the auxiliary shift T+alpha, because its sign proof works with absolute
values; (ii) the q-cube quotient normalization and absorbed padding of the
older two-root construction extend to the doubled product-square equation;
(iii) divisibility by q excludes the exceptional main index three before
transport, so the shift can also be deleted for the normalized bV weight.
Pell doubling, product-square extraction, and q-cube normalization themselves
are credited predecessors, not claimed as new here.

## 2. Complete polynomials and fixed coefficients

The four fixed integer coefficients beta,K0,MC,MF are the *whole* directly
indexed BFS943 tuple. Their exact compressed little-endian integer payloads
are in `coefficients/`; each circuit contains their bit lengths and SHA-256
hashes. The complete finite printed recipe, including the 436-character
machine seed, decoder, alphabet and 943 tiles, is retained in
`inherited/indexed_constant_recipe.tex`; the seed and literal tile list are
also retained separately. The native calibration proof is
`inherited/indexed_native_proof.md`. The largest coefficient is 592,884 bits.
The ports obey

    beta >= 31 odd, K0 > 0, 0 < MC < beta < MF < 2 beta.

These four numbers are fixed leaves, never existential unknowns. MF already
contains the source shift and must not be shifted again or combined with a
K0 from another tuple.

For the unnormalized 83-operation equation the only unknowns are

    J,F,alpha,i,T,w,Y,n,eta,zeta > 0.

For the normalized 80- and 81-operation equations replace the input Y by
s>0 and define Y=q^3 s. All other quantities below are polynomial
abbreviations, not extra unknowns:

    q = beta J + 1, h = q-1, C = q-F-alpha, X = wq,
    mu = q^2+1, k = eta+zeta, c = kY+eta,
    A = mu Y(X+1)+1, Delta = A^2-1, H = 4A-5,
    v = X mu^2 Y^2, E = 1+v(v+1)k^2,
    R = [h(q-F)+alpha](q^2-1)+(MC+q MF)J,
    e = k-R-1, B = (K0+w)C-F,
    U = i c^2, a = Delta U^2 E, F0 = 1+a, G = E F0,
    Fsq = 1+4aF0, Q = Delta(Fsq-1),
    b = cT-R, V = Fsq b-c, Kpos = X(3c-2X)+2.

Choose L=V^2 in the 83- and 80-operation equations, and L=bV in the
81-operation equation. In the unnormalized equation set

    P = q^3 h, M = P mu^2 H,
    Z = P mu^2[H(n-LB)+Kpos]
        +H[mu^2(hY-q^3 B)-P e].                         (1)

In the normalized equations set

    M = h mu^2 H,
    Z = h mu^2[H(n-LB)+Kpos]-H[mu^2 B+h e].              (2)

In each case the single complete equation is

    N = Q(Z^2-M^2 G V^2)+(M^2 G-Z^2) = 0.               (3)

Equivalently,

    N = (Q-1)Z^2-M^2 G(QV^2-1).                        (4)

There are no divisions, variable exponents, roots or inequalities inside
the polynomial. The strict positivity requirements specify its domain.

## 3. Inherited arithmetic interfaces and proof order

The preserved package-133 proof gives product-square root extraction and
its complete native composition. Its predecessor saturation proof supplies
the later rank/parity/denominator/projection chain. Two exact interfaces
are additionally retained because deleting T+alpha must not silently
invalidate a sign hypothesis:

* The main-folding lemma in `inherited/main_folding_proof.md`, Lemma 2.2,
  assumes A>=3, positive c,I,f, c<=I, the strong norm, an integral auxiliary
  norm, and V=-c modulo f. It allows either sign of V. The folding reduces
  an odd auxiliary index modulo twice the strong index, so its resulting
  index p is odd.
* `inherited/signed_index_lemma.md`, Sections 3-4, assumes the recovered
  main ordinate c=psi_A(p), the normalized strong divisibility c^2|I,
  0<p,R<c/2, and the two residues V=-c modulo f and V=-R modulo c. It
  allows either sign of V,y and does not mention T>alpha.

Thus neither interface needs the deleted shift. The native first-index,
whole-product projection and fresh unscaled reconstruction occur only
after the transport sign has supplied C>0 and the correct mask bounds.
The proof of consistency equivalence uses these specifically identified
ordinary results and their existing calibration, not an arbitrary choice
of a DPRM polynomial. The retained files are a selected ordinary proof
closure and exact tuple, not a new build of every transitive formal file.

## 4. Root recovery does not need the auxiliary shift

For every positive assignment, q>=32, c>=3, A>4, Delta>=3, E>1,
U>=c^2, a>c, F0>1, Q>c^2 and M>0. The defining identities are

    Fsq = (1+2a)^2,
    Q = 4 Delta^2 U^2 G,
    gcd(E,F0) = 1.                                     (5)

Put delta=Q-1 and Dy=QV^2-1, only as proof notation. If b=0 then
V=-c; if b is nonzero then |V|>=Fsq-c>1. Therefore Dy>0. At a zero
of (4), z=Z/M is a nonzero rational satisfying

    delta z^2 = G Dy.                                  (6)

Because G divides Q, both delta and Dy are -1 modulo G. Their product
is coprime to G. Each prime valuation of G is consequently even in (6),
so G=g^2 for a positive integer g. Coprimality in (5) gives

    E=tau^2, F0=f0^2, g=tau f0.

The positive rational y=|z|/g solves

    QV^2-(Q-1)y^2=1.                                  (7)

For completeness, the rational adjacent-Pell descent proves y integral.
Writing y=r/m in lowest terms gives m^2|(Q-1). With v1=|V|>1,
v1<y<Qv1/(Q-1); the norm-preserving transformation

    v2=(2Q-1)v1-2(Q-1)y,
    y2=(2Q-1)y-2Qv1

keeps v2 integral, preserves the reduced denominator m of y2, and has
-v1<v2<v1. It cannot have v2=0 because the norm is 1. Replacing signs
and descending reaches |v1|=1, where y=1; hence m=1. Thus

    z=epsilon g y, epsilon in {1,-1}.                  (8)

Define the proof-only integers f=1+2a and I=2Ug. Then

    f^2-Delta I^2=1, f^2=Fsq, Q=(Delta I)^2, c^2|I.     (9)

All main-folding hypotheses from Section 3 now hold, because the actual
V still satisfies V=f^2 b-c=-c modulo f. We obtain

    c=psi_A(p), p>=1 odd,
    k=2psi_(2v+1)(n0), n0>=1.

If n0=1, k=2 forces eta=zeta=1 and c=2Y+1, strictly between
psi_A(1)=1 and psi_A(2)=2A. Thus n0>=2 and

    k>=8v+4, c>kY>=k>8q^5, Kpos>0.                  (10)

This entire recovery uses neither the sign of b, nor C>0, nor n-s>0.

## 5. A sign-free transport lemma for L=V^2

First b cannot vanish at a zero. Otherwise V=-c, and (7) gives

    y^2=c^2+(c^2-1)/(Q-1),

strictly between c^2 and c^2+1 because c>1 and Q>c^2, contradicting
integrality of y. Hence b is nonzero. Since Fsq>c+1, V and b have the
same sign and |b|<|V|. The identity

    a^2-g^2 = E[Delta U^2 E(Delta U^2-1)-1] > 0

gives g<a. Also Fsq-c=1+4aF0-c>3a>3g. Consequently

    |V|>3g, y<(3/2)|V|, gy<V^2/2.                    (11)

The one-sided error bound survives without any shift:

    b-e=cT-k+1>0,
    rho=e/mu^2 < b/mu^2 <= |b|/mu^2 < |V|/mu^2.       (12)

Here c>k and T>=1. In particular no assertion e>=0 was made.

Set kappa=Kpos/H>0, t=B/h and W=1+hL. The exact rational carrier is

    Z/M=n+kappa+Y/q^3-Wt-rho                         (unnormalized),
    Z/M=n+kappa-Wt-rho                               (normalized). (13)

Suppose B<=-1. In both versions (8), (11)-(13) give

    n < gy+Wt+rho < V^2/2-V^2+|V|/mu^2 < 0,

contrary to n>0. The last inequality uses |V|>1 and mu^2>2. Thus B>=0,
and B=(K0+w)C-F with F>0 implies C>0. This proof establishes the
83/436 and 80/750 equations without invoking a fifth-index gap or a
positivity-preserving inverse affine substitution.

## 6. The normalized smaller weight L=bV

This version needs a stronger bound |b|>4g. It is proved before
transport, using q|X and q|Y, both literal identities in the normalized
chart. The argument is not valid as stated for an arbitrary free Y.

### 6.1 The main index three is impossible

Suppose p=3, so c=4A^2-1. If n0>=3, then

    kY >= 2psi_(2v+1)(3)Y > 32v^2Y,
    c < 4A^2 < 16mu^2 X^2Y^2,

since A<2muXY. But 32v^2Y=32X^2mu^4Y^5 exceeds the latter upper
bound, contrary to c>kY. Hence n0=2 and k=8v+4.

Let D=(X+1)^2-2XY. Expanding c=kY+eta=4A^2-1 gives

    eta=4mu^2Y^2 D+8muY(X+1)+3-4Y.                    (14)

The inequality eta<k rules out D>=2X: then
eta-k>=8muY(X+1)-4Y-1>0. Conversely D=1+X(X+2-2Y) cannot be zero
when X>=32. If D<=0, then D<=-1 and 2Y>=X+3, so X+1<2Y. Formula
(14) therefore gives

    eta < -4muY^2(mu-4)+3-4Y < 0,

another contradiction. Thus 0<D<2X. Since D=1+Xr for the integer
r=X+2-2Y, we have r in {0,1}, or

    2Y-X in {1,2}.

This is impossible because q divides both X and Y and q>=32. Therefore
p>=5, and in particular c>psi_A(3)=4Delta+3.

### 6.2 Excluding the third auxiliary index

Equation (7) with S=Delta I and Q=S^2 gives an odd auxiliary index j
such that |V|=chi_S(j)/S. Its first and third values are 1 and 4Q-3.
The first is excluded by (11). We have

    0<c-(4Delta+3)<Fsq,
    0<c+(4Delta+3)<Fsq.                               (15)

For the upper bounds, Fsq>4Delta c^4>c+4Delta+3 because U>=c^2,
E>1, Delta>=3 and c>=3. If V=4Q-3, the identity V=Fsq b-c implies

    Fsq(b-4Delta)=c-4Delta-3,

contrary to (15). If V=-(4Q-3), it gives

    Fsq(b+4Delta)=c+4Delta+3,

again impossible. Hence j>=5 and

    |V| >= 16Q^2-20Q+5 > 8Q^2.

Using c<Fsq, Fsq>2 and (9), this implies

    |b| >= (|V|-c)/Fsq
        > 8Q^2/Fsq-1
        > 4Delta^2(Fsq-1)-1
        = 4Delta^3 I^2-1 > 4g.                       (16)

The last step uses I=2Ug, with Delta,U,g positive.

### 6.3 Transport and positivity

Since sign(b)=sign(V), L=bV=|b||V|>0. By (7) and (16),

    gy < (3/2)g|V| < 3L/8 < L/2.

The same one-sided bound (12) gives rho<|b|/mu^2<L/2. If B<=-1,
then Wt<-L, so (13) yields n<L/2-L+L/2=0 strictly. Therefore B>=0
and C>0 for this third equation also. The lower-degree weight is now
licensed without the deleted T+alpha gate.

## 7. Ordered source recovery and completeness

Once C>0, the retained literal mask bound supplies 3q<R<q^4-2.
Together with (10) and Pell growth this gives 0<p,R<c/2. Strong
classification and c^2|I give f=chi_A(m), I=psi_A(m), pc|m and
m>2p. The actual congruences remain

    V=-c modulo f, V=-R modulo c,

the second because f^2=1 modulo c. The signed-index lemma therefore
gives p=R. This interface explicitly allows either sign of V and never
uses T>alpha. Oddness of R gives q even and J odd. Only now invoke
gcd(mu^2,hH)=1 (with q a unit modulo mu in the unnormalized chart).

The integer carrier (8) forces mu^2|e. The unchanged first-index
congruence and ratio argument then give n0=(R+1)/2 and the inherited
strict whole-product bound. In the normalized chart the remaining
carrier gives H|h Kpos, which in particular gives the old weaker
premise H|q^3 h Kpos. The same projection forces X=2^R by bounding
the *entire* divisible product; no nonunit is cancelled modulo H.
It also makes kappa integral. The last fractional term gives h|B
because W=1 modulo h. In the unnormalized chart the same inherited
partial-fraction argument also yields q^3|Y; in the normalized chart
this was built in from the start. The fixed-minus parity, exact
half-binomial rounding and fresh unscaled source reconstruction have
all their original hypotheses, and yield a finite ZFC refutation.

For completeness, start with a finite refutation and use package 133's
complete canonical converse with the identical four coefficients and
the same choice of weight. This provides positive old coordinates,
including T_old, n_old and q^3|Y. Set

    T_new=T_old+alpha.

For the unnormalized equation retain all other coordinates. The entire
kernel and equation are identical, so this is a positive new zero.
For either normalized equation additionally set

    s=Y/q^3 > 0, n_new=n_old+s > 0.

The exact free polynomial substitutions are

    Y_old=q^3 s, T_old=T_new-alpha, n_old=n_new-s,
    Z_old=q^3 Z_new, M_old=q^3 M_new,
    N_old=q^6 N_new.                                  (17)

Since q>0, the new equation vanishes. The old shifted coordinates in
(17) need not be positive at an arbitrary new zero; that is why
Sections 4-7 supplied a direct soundness proof instead of assuming a
positive inverse shear.

We have proved both existential directions. Composing with the named
whole native/refutation calibration yields the asserted ZFC equivalence
for each exact fixed polynomial. This is a consistency encoding, not a
proof that the equation has or has no solution.

## 8. Exact cost and degree

The 83/436 circuit removes exactly the one Tp=T+alpha gate from package
133's 84/436 circuit and redirects its single consumer. Every remaining
gate and all ten inputs/four ports remain live. In the normalized graphs,
Y=q^3 s adds one gate; moving existing q^2,q^3 earlier costs none.
Deleting P=q^3h and simplifying the numerator saves four gates. Net
normalization saving is three. The bV variant pays one extra product
relative to V^2, which is already needed by the finalizer. Exact totals
are (multiplications, additions, subtractions)=(50,18,15), (48,18,14)
and (49,18,14), respectively.

All inputs have degree one and all fixed coefficients degree zero.
The key global degree bounds are:

| Quantity | Free-Y chart | Normalized chart |
|---|---:|---:|
| A, Delta, U, E | 5,10,5,18 | 8,16,11,30 |
| a, F0, G, Fsq | 38,38,56,76 | 68,68,98,136 |
| Q, b, V, M | 86,4,80,13 | 152,6,142,13 |
| Z with L=V^2 | 175 | 299 |
| Z with L=bV | not used | 163 |

For L=V^2, (Q-1)Z^2 uniquely dominates: degree 436 or 750, whereas
M^2G(QV^2-1) has degree 328 or 560. For the normalized bV equation,
the latter term uniquely dominates at degree 560, while (Q-1)Z^2 has
degree at most 478. Thus no cancellation between the two top summands
can alter these bounds.

Write q0=beta J and k0=eta+zeta. The entire highest homogeneous forms are

    83/436:
      2^14 q0^200 w^46 Y^104 i^20 k0^60
           (q0-F)^4(q0-F-alpha)^2;

    80/750:
      2^14 q0^506 w^46 s^108 i^20 k0^64
           T^4(q0-F-alpha)^2;

    81/560:
      -2^10 q0^384 w^34 s^80 i^14 k0^46 T^2.           (18)

Each is nonzero for the actual positive beta. For example, select
eta to its full k0 exponent and alpha^2 in the first two displayed
final factors; the resulting coefficients are nonzero integer multiples
of beta^200, beta^506 and beta^384. Formula (18) proves attainment of
all three upper bounds. Notice that in the normalized chart cT has
degree six and dominates R, of degree four; simply substituting into
the old *unweighted* leading term would give an incorrect degree proof.

## 9. Verification, provenance and limits

Run `python3 -B verify.py` or `python3 -B -O verify.py`. A receipt can be
written with `--output /absolute/path/receipt.json`. The checker uses
the standard library, imports no builder mathematics, verifies the whole
fixed integer tuple and source hashes, proves ten exact free polynomial
identities by collection over Z, checks all graph references and liveness,
independently evaluates the complete displayed formulas, checks parent
substitution controls at both signed and positive inputs, proves degree
upper bounds gate by gate, and collects exact complete univariate
specializations that certify the stated leading forms are attained.
It rejects twelve actual gate mutations and checks deterministic byte-exact
builder replay. There are no assertions that disappear under Python -O.

The independent complete-ray checks corroborate (18); they are not used
as a substitute for a global degree upper bound. Numerical spot checks
do not prove the Pell or calibration theorems. The unbounded arguments
above are ordinary proofs, separately reviewed within the AI-assisted
workflow. They are not independent human endorsements.

All copied material retains its source identity in SOURCE_LEDGER.json.
The mathematical derivations of the 80- and 81-operation equations build
on two specifically attributed predecessors; the result is a measured
new combination and a newly proved auxiliary-shift deletion. No claim
that earlier general mechanisms were previously unknown is made.
