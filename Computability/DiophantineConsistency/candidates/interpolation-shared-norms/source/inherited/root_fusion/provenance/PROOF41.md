# A quartic in 41 unrestricted integer unknowns

## The equation and precise claim

`quartic41.json` specifies 41 unrestricted integer unknowns and 26
quadratic residuals. Let Q41 be their sum of squares. The exact fixed
coefficient binding is the whole source34
`mixed-parity-unrounded-1064921` tuple, with beta=2^1064921-1 and the
shifted high mask MF. The four payloads are supplied in `coefficients/`
and regenerated from the source tile list by the verification code.

Ordinary mathematics formalizable in ZFC proves

    (Q41 has an integer zero) iff (ZFC has a finite refutation).

Consequently absence of integer zeros is provably equivalent in ZFC to
Con(ZFC). Its exact degree is four because [tau^4]Q41=1. Relative to the
inspected source57 quartic45, it saves four unrestricted integer variables
and two quadratic residuals at the same degree. This is not a global
minimum or a new proof-assistant kernel certificate.

## 1. Relation to the new quartic44

The complete intermediate construction and its proof are in
`quartic44.json` and `PROOF44.md`. It differs from source57 by using
X=2u^2 as the positive power guard and delaying recovery of the radix sign.

Starting with that intermediate system, make two changes:

1. In every arithmetic row replace its source coordinate w by 4 w_scale,
   where w_scale is one unrestricted integer replacing w. This affine
   substitution does not change the number of coordinates or the maximum
   residual degree.
2. Remove the two positivity guards for eta and zeta and their six private
   coordinates. Replace them by the one quadratic equation

       eta zeta = 1+e1^2+e2^2+e3(e3+1).

   This uses three private coordinates, denoted eta_zeta_pos1,...,3 in the
   literal packet.

Thus 44-6+3=41 unknowns and 27-2+1=26 residuals remain. The product guard
forces eta,zeta to have the same nonzero sign. The new large scale is
precisely what excludes the remaining possibility that both are negative.

## 2. Sign-free preliminary facts

Suppose all new residuals vanish. Put

    q=beta J+1, Q=|q|, C=q-F-alpha,
    w_source=4 w_scale,
    s=2 v_scale+1, i=2r+1,
    X=q w_source=2u^2, Y=sq^3, E=XY,
    k=eta+zeta, c=kY+eta, a=(X+1)Y,
    A=a+2, H=4a+3, Delta=A^2-1,
    D=X+ac+gamma H,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J.

The common-sign F alpha and F C guards are unchanged. PROOF44 Sections
2--3 establish Q>=16 and

    Q(Q^2-1)<R<Q^4-2, R>3Q+3,                     (1)

without using eta,zeta, the sign of q, or a transport guard. Since s is
odd, |Y|>=Q^3 and Y is nonzero. Also X>=0. If X=0, the unchanged main
norm and its reduction modulo H give 0=1 mod H, impossible because
|H|=|4Y+3|>1. Thus X>0.

The identity X=4q w_scale now implies w_scale nonzero and

    X>=4Q, |E|>=4Q^4>3R+1.                         (2)

This strengthening from |E|>R+2 to |E|>3R+1 is the only new quantitative
hypothesis needed to combine the two signs of eta,zeta into one guard.
It is obtained with an affine reparameterization, so no new existential
coordinate or higher-degree constraint is introduced.

## 3. Excluding the negative common sign

Assume eta,zeta<0. Write

    eta0=-eta>0, zeta0=-zeta>0, K=eta0+zeta0=-k>0,
    Z=|Y|, B1=|A|, c0=|c|, P0=2XY^2+1.

If Y>0 then c0=K Y+eta0, so

    K Y<c0<K(Y+1).

If Y<0 then c0=K Z-eta0, so

    K(Z-1)<c0<K Z.

In both cases c0>K, B1>=2, Delta=B1^2-1>0, and P0>B1. These inequalities
follow directly from X>=4Q>=64 and Z>=Q^3>=4096; in particular
`P0-B1 >= 2XZ^2+1-((X+1)Z+2)>0`.

The unchanged first and main Pell norms classify their absolute coordinates
as

    |tau|=chi_P0(n), K=2 psi_P0(n), n>=1,
    |D|=chi_B1(p), c0=psi_B1(p), p>=1.

Here chi and psi are the ordinary Pell polynomials, with
`chi_b(t)+psi_b(t)sqrt(b^2-1)=(b+sqrt(b^2-1))^t`.
Since P0>B1 and c0>K, monotonicity gives p>n: if p<=n then
`c0=psi_B1(p)<=psi_B1(n)<=psi_P0(n)=K/2`, a contradiction.

The index row is still k=R+1+hE, with h unrestricted. Since
P0=1 modulo |E|, the Pell recurrence gives psi_P0(n)=n modulo |E|.
Because k=-K, it follows that

    2n = -(R+1) modulo |E|.

The left side is positive and 0<R+1<|E|. Thus there is an integer v>=1
with `2n=-(R+1)+v|E|`. By (2),

    2n >= |E|-R-1 > 2R, hence n>R.                 (3)

We will now recover the main rank p=R independently of either sign of c.
The inequality p>n>R gives p>=6 by (1). The standard Pell growth bound
`psi_B1(p)>=(2B1-1)^(p-1)` yields

    c0>B1(B1^2-1)^2, c0>2p, c0>2R.                (4)

For example the first bound follows already at p=6 because
`(2B1-1)^5>B1^5>B1(B1^2-1)^2` for B1>=2. The second bound holds at
p>=6 and B1>=2 by the same recurrence/growth estimate.

The unchanged ordinary strong equation is

    (i c^2)^2=Delta(f^2-1), i=2r+1 nonzero.

By the inherited ordinary strong-rank lemma, with (4) as its explicit
size hypothesis,

    |f|=chi_B1(m), p|m, c0|m, m>=c0>2p.

Put rho=|i|c0^2. The auxiliary equation and exposed quotient rows are

    rho^2 V^2-(rho^2-1)y^2=1,
    V=of-c, V=jc-R.

This is exactly the signed auxiliary step-down situation from
`upstream/SIGNED_DOMAIN_29.md`, "Signed auxiliary quotient", and the
ordinary-strong version identified there. Its proof is sign-insensitive
in c: the first congruence is squared, replacing c by c^2=c0^2, and the
second is modulo c0. More explicitly the odd auxiliary Pell index ell
satisfies ell=+p or -p modulo m and ell=+R or -R modulo c0. Since c0|m,

    R=+p or -p modulo c0.

Both R and p are strictly between zero and c0/2 by (4), so p=R. This
contradicts p>n>R from (3). Therefore eta,zeta cannot both be negative.
Their positive product excludes zero and opposite signs, so

    eta>0 and zeta>0.                               (5)

This use of |E|>3R+1 is essential. Merely dropping the two original guards
without increasing the scale leaves a possible negative-index wrap and
is not justified by the inherited proof.

## 4. Soundness by restoring the intermediate system

Given (5), represent eta and zeta separately by the standard ternary
positive form Pos. Set the intermediate coordinate w to 4 w_scale and
leave every other coordinate unchanged. All residuals of quartic44 now
vanish: its retained rows are exact affine substitutions of the new ones,
and its two omitted positivity guards have just been supplied.

PROOF44 therefore yields a blank K215 halt and a finite ZFC refutation.
In particular its absolute-radix argument first recovers X=2^R, then uses
`-2^t != 1 mod (2^d-1)` for d>=3 to force q>0. No premature assumption
that q or w_scale is positive is made here. Its corrected literal
transport identity is `(K0+w)C=z(q-1)+F`, as independently audited.

## 5. Completeness and the divisible-by-four scale

Conversely, a finite ZFC refutation supplies the canonical witnesses of
source34. They have q=2^t with t odd, R=3 mod4, R>t, X=2^R, and

    w_source=2^(R-t).

Because R and t are odd and R>t, their difference is a positive even
integer and hence at least two. Thus w_source is divisible by four;
choose `w_scale=w_source/4`, a positive integer. Choose
`u=2^((R-1)/2)` exactly as in quartic44 completeness. The canonical eta
and zeta are positive, so their product admits one ternary Pos
representation. Supply its three new coordinates and retain every
unchanged canonical coordinate. All 26 new residuals vanish.

No consistency assumption enters any coefficient or witness recipe. This
completes the existential equivalence and hence the ZFC-provable
unsolvability/consistency equivalence.

## 6. Exact checks and proof boundary

Run the following in the extracted directory:

    python3 build_verify44.py
    python3 build_verify41.py

Both also run with Python's -O flag. The first reconstructs the source
tuple and intermediate packet. The second checks all source Git blob
identities, rechecks the actual coefficient SHA256 digests, emits the
41-variable packet, proves every retained row is the exact w=4 w_scale
substitution of its quartic44 counterpart, expands the sum of squares
with symbolic coefficient ports, checks all variables are live, and
certifies degree four via its literal tau^4 coefficient. The expansion is
provided as `certificates/QUARTIC41_EXPANSION.json`.

These finite checks certify algebra, fixed data, liveness, and degree.
The universal Pell arguments, native compiler, and ZFC calibration are
the named mathematical dependencies in this proof and PROOF44. No new
end-to-end Lean/Rocq certificate or internally encoded ZFC derivation is
claimed. The reduction is a proposed research contribution with internal
AI-assisted checking, not externally peer-reviewed mathematics.
