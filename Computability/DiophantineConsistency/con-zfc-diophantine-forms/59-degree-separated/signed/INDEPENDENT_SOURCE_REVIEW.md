# Independent review of signed source positivity and spectator bootstrap

## Disposition

PASS for the frozen canonical 520-operation variant in section.tex, with
pad B^2162, block L=2bB^2279, and N=eta b B^1201. This review is independent
AI-assisted review within the project, not external human review or a new
end-to-end proof-assistant certificate. It checks the source and bootstrap;
the inherited Jones ratio/compiler interfaces remain explicit dependencies.

The optional compact 518-operation variant is not covered by this initial
review unless a separately marked addendum below says otherwise.

`check_source_minimum_independent.py` proves three universal polynomial
completion/expansion identities without importing the construction program.
It also checks exact rational constants, degree gaps, source metadata and
parity formulas. The updated checker runs 192 bounded exact-integer source stress tests across both variants, including
negative packed inputs and integers adjacent to the exact quadratic minimum.
Those samples are diagnostics; the all-integer argument is given below.

## 1. Completing the source quadratic, not merely its high word

Write A=D2(B), D=D1(B), C=D0(B), n=N0, e=ell, P=B^2162, and T=Targets.
Let u=e+g. The exact source is

    Gplus=A u^2+D u+C+P,
    Sc=u-e+n(2Gplus+T).

The following identities are checked over an independent polynomial ring:

    2A Gplus-A^2 u^2=(Au+D)^2+2A(C+P)-D^2,
    Sc=a u^2+b u+c,
    4a Sc-(2a u+b)^2=4ac-b^2,

where a=2nA, b=2nD+1, c=2n(C+P)+nT-e. These identities include the
signed linear g term. Positivity of Gplus by itself would not suffice.

For coefficient bound Cstar=2^2134927 and B=8192 Cstar bbase^2, the
certified kernel degrees and positive leading coefficient give

    D2(B)>(1/2)B^1929,
    |D1(B)|<2Cstar B^2027, |D0(B)|<2Cstar B^1719.

Completing only half of the positive quadratic gives, for every real u,

    Gplus>(1/4)B^1929 u^2+B^2162
           -4Cstar^2 B^2125-2Cstar B^1719
         >(1/4)B^1929 u^2+(1/2)B^2162.

The last step is valid because the normalized losses are
4Cstar^2/B^37<1/4 and 2Cstar/B^443<1/4. Their strict inequalities follow
already from B>=8192 Cstar and Cstar>=1; the much stronger actual base
causes no hidden side condition.

Now g and ell are integers, so u is an integer. Consequently

    Sc>(n/2)B^1929 u^2+u+nB^2162-ell>0.

Indeed t u^2+u>=0 for every integer u whenever t>=1. Here
 t=(n/2)B^1929>=1. The remaining constant is positive since ell<n.
This proves Sc>0 for every integer g before any sign guard or digit recovery.
The proof does not restrict g to a bounded interval prematurely.

## 2. Mask and unconditional R bound

Distinct labels lie in 1..116, so
ell<2B^116<N0=B^117. More precisely
ell<=sum_(i=1)^116 B^i. Because 1<bbase<B,

    0<Mc=N0-1-(bbase-1)ell<N0.

The high mask is positive, so Tc>0. With L=2bbase B^2279>1,

    R=L^2+Sc(L-1)+Tc L+L-1>L^2.

This inequality is unconditional in all signed inputs except epsilon!=0,
which gives bbase=2epsilon^2>=2. In particular it is available in the
potential a1=0 spectator branch.

Using eta=2^(8kappa-10) and B=2^kappa bbase^2,

    N^2=2^(-20) a^15 B^2403<B^2418<B^4558<L^2.

Also bbase<=cap=bbase B^116<=N. Thus R>=N>=8 and the needed source
ceilings hold without already knowing any of s,phi,Delta are positive.

## 3. Retaining exponent 2279 despite the added pad

After the interval guard supplies 0<g<cap=bbase B^116, one has
u=ell+g<2bbase B^116. The three kernel bounds then imply

    |G|<12Cstar bbase^2 B^2161,
    2|G|<B^2162/256,
    Targets<B^2162/256.

The numerical constant is sound:24/8192<1/256. Hence
Jc<(2+1/128)B^2162. Since g<N0 and B^2162>128,

    0<Sc<3B^2279.

Distinct targets at most2129 imply
(B-2)Targets<B^2130, so Tc<N0(1+B^2130)<B^2279. Therefore

    Sc+Tc<4B^2279<=2bbase B^2279=L.

The first inequality is strict, including the boundary bbase=2, so the
three R blocks are disjoint. Increasing the off-target degree by one does
not force an increase of the overall block exponent to2280.

## 4. Carry and parity calibration

After power-of-two recovery, each recovered coordinate p_i=n_i+1 is at most
bbase. Including the added coefficient1, every coefficient h of Gplus has
absolute value below994 Cstar bbase^2<B/8;994/8192<1/8.
The sparse padding digits2h+target_indicator normalize with incoming carry
only0 or-1. At a target, the allowed digits0 or1 occur exactly for h=0,
independently of the incoming borrow. The top added term is off-target and
does not change any residual identity. Its positivity also terminates the
borrow chain.

The low mask population is117nu-31k and the high mask population is
22(nu-1), giving139nu-31k-22. With L=2^lambda and
lambda=1+k+2279nu, the threshold is

    lambda+popcount(Tc)+1=2418kappa+4806k-20.

The chosen N has twice its base-two logarithm exactly equal to this:

    2[(8kappa-10)+k+1201(kappa+2k)].

All constants and exponents match. Thus the central-binomial square
threshold is not merely an asymptotic or rounded estimate. The source
coefficient and row identities remain those of the original coherent tuple.

## 5. Spectator bootstrap is noncircular

At a final zero, Sigma=0 is impossible because the nonzero homogenized
intersective polynomial would leave Theta^4. Thus epsilon,w,i,z1,z2,z3,a0
are nonzero. Each d_j is2 modulo3 and each guard B_j is1 modulo4, so none
vanishes. The prefix C2 and final Cstar are nonzero.

The final spectator guard satisfies gcd(B3,a1)=1. If a1!=0, then B3!=1
because all of d3,C2,a1,z3 are nonzero; and B3!=-1 because it is1 modulo4.
Thus Cstar=a1 would force B3=+/-1, a contradiction. If a1=0, Cstar!=a1
already follows from Cstar!=0. Hence the two radicands are unequal before
any positivity claims.

The raw two-root norm therefore has a nonzero rational sum q=X/Sigma.
The explicit rational formulas for its two roots show Cstar and a1 are
integer squares, with Cstar>0 and a1>=0. They also show q is integer and
Sigma divides Theta. No argument assumes independent complex conjugates.

The factors a0,B1,B2,B3 are pairwise coprime. Their nonzero positive square
product makes each absolute factor a square. Since a negative square is
never1 modulo4, all B_j are positive; the product sign then gives a0>0.
The first two nontrivial guards force d1,d2>0 and therefore s>=1,phi>=0.
The last guard must not yet be used: if a1=0, it would equal1.

At precisely this point, the unconditional source result above gives R>0.
Together with epsilon,w!=0 and s>=1, it gives U,Y>0, A>=2, and C>0.
Consequently

    D>=A^2>0, F>=1, CD+1-A>0, G>=A>1, I>=1.

Thus a1=DFI>0. Only now does positivity of the final guard force d3>0,
which gives Delta>0. This closes the zero-spectator case without adding
a1 to the nonzero multiplier and without assuming the interval guard first.

## 6. Dependency boundary

The source proof and spectator bootstrap pass. The broader ordinary Jones
ratio soundness/completeness, CRT reparameterization, intersective polynomial,
and native compiler theorem are separately identified dependencies in the
author's section. This local review did not replace them by finite tests.
Any later compact padding/block change needs its own clearly identified
calibration check rather than silently reusing this frozen receipt.

## 7. Compact odd-parity addendum: PASS

The separately reviewed `COMPACT_CALIBRATION_PROOF.md` and
`generated/signed_coprime_compact_split_crt.json` replace only P by B^2161,
L by B^2279, and the circuit register N by n_hat=eta epsilon B^1201.
The following checks close the additional obligations.

1. The half-quadratic completion uses losses 4 C^2 B^2125 and
   2 C B^1719. Their gaps to the new padding are still 36 and 442.
   Thus Gplus > B^1929 u^2/4+B^2161/2, and the same integer inequality
   t u^2+u>=0 proves Sc>0 for every integer g. No positivity of g is
   assumed in the spectator bootstrap.
2. The proof parameter is N=abs(n_hat)>0, whereas the polynomial uses
   no absolute value. Independent inspection of the emitted DAG confirms
   that the N register has exactly one consumer, its own square. Thus
   replacing its sign on the proof side changes no ratio expression.
   The exact inequalities N^2=2^-21 a^16 b B^2402 < B^2418 < L^2,
   b<=c<=N, and N>=8 hold before binary recovery for epsilon!=0.
3. For 0<g<c, the two error terms 2abs(G) and Targets are each below
   B^2162/256, and 2B^2161<B^2162/128 because B>256. Their sum is
   strictly below B^2162/64. This gives Sc<B^2279/32 and
   Tc<B^2279/64, hence the required Sc+Tc<L. The coefficient bound
   994 C b^2<B/8 includes the smaller off-target padding coefficient.
4. Recovering b=2^k from the Jones theorem forces k odd, since
   b=2epsilon^2 with epsilon a nonzero integer. With nu=kappa+2k,
   the threshold is exactly 2418kappa+4805k-21, equal to
   2(8kappa-10+1201nu)+(k-1)=log2(n_hat^2). Completeness chooses
   epsilon=2^r, giving a cofinal set of odd k. Even k is not silently
   required by the proof.
5. The spectator argument in section 5 uses only the established positive
   proof parameter and unchanged source/guard expressions. It therefore
   transfers without a new zero or negative branch.

The independent checker now checks both calibration identities, both
padding gaps, both operation ledgers, the square-only N use, and 192 exact
source stress cases, 120 of them with negative g. Normal and optimized
Python runs agree byte for byte. These finite diagnostics supplement, not
replace, the universal proof above. This review certifies the source and
calibration changes of the 518-operation variant; its whole-polynomial
degree witness and inherited ratio/compiler dependencies remain separately
identified in the author's construction and checker.
