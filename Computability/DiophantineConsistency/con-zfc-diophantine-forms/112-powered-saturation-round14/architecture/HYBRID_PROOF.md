# Reciprocal prime-power CRT with a carrier-derived amplification budget

## Status and theorem boundary

This is a complete existence-preserving arithmetic replacement of the frozen
direct C222 eight-column certificate interface. It uses neither K215 nor a
Jones universal equation. Its interpretation as refutability of the particular
ZFC calculus inherits the explicit C222 calibration, Horn-flow certificate,
eight-column projection, simultaneous positive-power/Pell graph, binomial digit
graph, and nonnegative contraction theorems from the supplied releases. It does
not supply a new Lean proof of those inherited statements. Subject to exactly
those existing ordinary proofs, the materialized natural-number polynomial
vanishes if and only if the calibrated calculus has a finite refutation. No
consistency or inconsistency assumption is used.

The new arguments below are proved in both directions. Finite tests are
regressions, not a substitute for these quantified proofs.

## 1. Reciprocal moduli at the small horizon

Let t >= 1, F=t!, T=F^2, and, for 1 <= i <= t, set

    d_i = 1 + T/i,              B = binom(T+t,t).

Since i divides F, d_i=1+F(F/i) is an integer congruent to 1 modulo F.
Consequently every prime dividing d_i is greater than t. If a prime p divides
both d_i and d_j, it divides i*d_i-j*d_j=i-j; this contradicts p>t for i != j.
Thus the d_i are pairwise coprime, and their product is precisely B. In
particular B >= 2.

This needs only t!, not the factorial of the complete source-evaluation bound.

## 2. Prime-power range decoding

For a prime p and positive e,k, and any natural a,

    p^e | binom(a,k)  implies  a mod p^e < k.

Use binom(a,k)=0 when a<k. Otherwise the valuation of the binomial is the
sum, for j>=1, of

    floor(a/p^j)-floor((a-k)/p^j)-floor(k/p^j).

Every summand is 0 or 1. If the interval [a-k+1,a] contains no multiple of
p^e, then for j>=e it contains no multiple of p^j, and every such summand
is zero. The valuation is at most e-1, a contradiction. Therefore a-r is
divisible by p^e for some 0<=r<k, proving the claim. This is a one-sided
implication; its converse is false and is not used.

## 3. The hybrid bounded-universal theorem

Let local bounds b_j be natural, and let K >= max(t,b_j+1,1). Let L be an
integer polynomial, with additional fixed natural parameters suppressed, such
that 0 <= L(i,w) < 2^K whenever 0<=i<t and 0<=w_j<=b_j. Put N=B^K.
Then these statements are equivalent:

1. For each 0<=i<t there is a bounded tuple w with L(i,w)=0.
2. There are positive C,A_j <= N^2 satisfying

       B | C+T+1,
       N | binom(C,t),
       N | binom(A_j,b_j+1),
       N | L(C,A).

Soundness does not need the representative upper bounds. Fix i in 1..t,
choose any prime p dividing d_i, let m=v_p(d_i), and let e=Km. The first
congruence gives C=-(T+1)=i-1 modulo p. The range lemma gives
C=s modulo p^e with 0<=s<t. Because p>t, necessarily s=i-1. The remaining
range conditions similarly give A_j=w_j modulo p^e with 0<=w_j<=b_j.
It follows that p^e divides L(i-1,w). Since p^e>=2^K>L(i-1,w)>=0, this
value is zero.

For completeness, choose one tuple for every row. CRT gives positive
representatives C,A_j in [1,B^(2K)] with

    C=i-1 mod d_i^(2K),        A_j=w_(i-1,j) mod d_i^(2K).

The first and last displayed congruences in (2) follow immediately. For a
range lower index k, a chosen representative is congruent to a member of
[0,k-1] modulo p^(2Km). If a<k its binomial is zero. Otherwise its falling
factorial has a factor of valuation at least 2Km. The denominator k! has
valuation at most k-1 <= K-1 < Km. Thus the binomial has valuation at least
Km. This proves every range divisibility simultaneously for all primes
dividing B. The representative bound follows from B^(2K)=N^2.

The old reciprocal canonical index C=B-T-1 cannot replace the variable C in
this theorem: for t=2, F=2, T=4, B=15 it is C=10, which is 0 modulo 5
but not modulo 25. The index range is essential and retained.

## 4. A new amplification budget forced by the existing carrier

The unchanged direct source defines

    M0+1 = ((t+1)^t)^ell,      R=2+t+x+y+M0,

where t>=1. Its printed local majorant is L(i,w)<R^E. The finite
coefficient recipes give ell=4194304 and E=8388608 in both the current
Cantor and square-shell variants. More generally it suffices that

    ell>=8,                 E<=2*ell.

The carrier, already required for Horn-flow multiplicity separation, gives
R>=2^ell. For all integers r>=2^ell,

    r^E < 2^r.                                             (A)

To prove (A) at r0=2^ell, observe that 2^ell>2*ell^2>=E*ell for ell>=8;
the first inequality at ell=8 persists by induction. Hence
r0^E=2^(ell*E)<2^r0. Also r0>=2E. For r>=r0,

    (1+1/r)^E <= sum_(j=0)^E (E/r)^j < 2.

Thus (r+1)^E < 2*r^E < 2^(r+1), proving (A) by induction.

Consequently the entire old affine budget K=8388608*R may be replaced by

    K=2R.                                                   (B)

The spare factor 2 is for the economical common radix, not local vanishing.
All range lower indices satisfy 1<=k<=R-1, and K dominates them. The proof
of (A) is used only after the actual carrier power has been recovered from
the independent simultaneous-power graph. It is not a presupposition about
an unvalidated binomial value.

## 5. One self-bounding factorial and a noncircular common radix

The proposed output F of t! defines rho=F*t^2. Request

    V=(rho+1)^t,             D=binom(rho+t,t),

and impose the two natural ceiling rows

    V+D=D*F+u+1,            D=u+v+1.                       (C)

The inherited self-bounding factorial lemma says exactly that these rows,
with the stated V and D, force F=t!, and supplies u,v when F=t!.
Its elementary proof uses

    V/D=t! * product_(i=1)^t (1-(i-1)/(rho+i))

and sum (i-1)/(rho+i)<1/(2F), after F>=1 has been established.

Retain the aggregate bound for the nine positive representatives,

    C + sum_j A_j + g = 9N^2,

and choose one common radix

    q=N*(N+V+1)^K.                                         (D)

The literal source includes C+T+1=B*iq, with T=F^2. It therefore forces
B>0 before B's binomial meaning is known, without a separate B>=2 guard.
The base rho+1 is positive regardless of the proposed F, so the shared
positive-power graph first yields V>=1. The raw ceiling rows give D>=1
and V+v=D*F, hence F>=1. Recover N=B^K>=1 and the power in (D), obtaining
q>V^K>=V^2 and q>V. This order uses only positive bases already justified
by raw equations. All other bases are q or q+1, the positive source
carrier base t+1, or rho+1.

Now rho>=t, and for 0<=j<=t,

    binom(rho+t,j) <= binom(rho+t,t) <= (rho+1)^t=V<q.

Thus the first exact digit is correct; (C) gives F=t!.
Next, even without using the intended value of B,

    F^2+t <= (F*t^2+1)^2=(rho+1)^2.

For every 0<=j<=t, binom(F^2+t,j) <= (F^2+t)^t <= V^2<q.
The second exact digit is therefore correct, establishing the reciprocal
product B and its lower bound B>=2. In particular N>=2^K.

For every representative n and every needed digit 0<=j<=k<=R-1,
the aggregate bound and K=2R yield

    binom(n,j) <= n^k <= 9^k*N^(2k)
                       < 2^(4R)*N^(2k)
                       <= N^(2k+2) <= N^K < q.

If j>n the coefficient is zero. This validates all nine fused range
graphs; N divides q, so their quotient-multiple condition is precisely
N|binom(n,k). There is no circular use of the binomial defining B or of
the ranges under validation.

## 6. Constructive completeness of the complete arithmetic replacement

Given a finite direct source certificate, retain its t,x,y,M0 and bounded
rows. The already established carrier relation gives the majorant in
Section 4. Set K=2R, F=t!, T=F^2, B=binom(T+t,t), and N=B^K. Choose
C,A_j by Section 3, and let g=9N^2-C-sum A_j>=0. Set rho,V,q as above.
The exact factorial lemma supplies u,v, and the carry-free bounds in
Section 5 supply the ordinary digit quotients and remainders. The first
index quotient is (C+T+1)/B, a positive integer. Because the source
polynomial is nonnegative on natural inputs, its multiple of N has a
natural quotient. Finally the inherited simultaneous Pell-power theorem
provides a common frame and all seed-index witnesses for this finite
family of true positive powers. No stronger existence claim is assumed.

Conversely a zero of the generated sum of squares sets every quadratic
residual to zero. Recover the powers and interpret the two exact digits
in the order above; validate all range divisibilities; then Section 3
recovers every bounded source row. The unchanged direct-source theorem
recovers a finite refutation. The independent contraction certificate
restores every deleted coordinate as an explicitly certified nonnegative
integer polynomial, so it preserves both directions over the naturals.

## 7. Reproduced finite endpoints

For each endpoint, the one equation is the sum of squares of the complete
quadratic residual list in natural/equation.json, or equivalently the
collected literal coefficient list in natural/expanded_polynomial.json.
All listed unknowns range over the nonnegative integers.

| Syntax | Unknowns | Residuals | Degree | Monomials | Coefficient height |
|---|---:|---:|---:|---:|---:|
| Cantor | 360 | 282 | 4 | 7343 | 83853107 |
| Square shell xx0 | 361 | 283 | 4 | 7282 | 7002692 |

Both use 19 positive-power requests, two exact-binomial requests, nine
range requests, one factorial, 15 independently tested Pell indices and
one derived index. Natural numbers include zero; this is not yet an
unrestricted-integer endpoint. Simple blanket four-squares substitution
would give a valid but uncompetitive 1440/1444-integer degree-eight pair.

The completed contribution is the combined arithmetic theorem, the
carrier-budget lemma, and these literal endpoints. The earlier 363-natural
reciprocal endpoint has fewer monomials; none of these comparisons is a
global minimality claim.

## Sources

- Frozen supplied ConZFC_Prime_Power_375_553, proofs/AMPLIFIED_CRT_PROOF.md:
  one-sided range lemma, amplification, and precision-2K CRT completeness.
- Frozen supplied ConZFC_Shell_Reciprocal_660,
  proofs/reciprocal_moduli_proof.md and proofs/shared_radius_proof.md:
  reciprocal product, self-bounding factorial, norm-product compression.
- Its upstream/ConZFC_407_888_Quartics/code/build_projected.py and inherited
  proofs: eight-column source, carrier and local majorants, arithmetic compiler.
- Public comparison pin: VladimirReshetnikov/ProveIt,
  84e16e43092614bae262ca59651cb9d77e31a255,
  Computability/DiophantineConsistency/README.md. The Library manuscripts
  above are ahead of that public tree. No claim of worldwide priority is made.
