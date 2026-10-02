# Integrated article and Lambert inverse audit

Audit date: 2026-10-01 (UTC).

## Verdict

PASS on the mathematics. The integrated article faithfully incorporates the
approved radius/barrier proof and the independently approved full-root/error
upgrade. The additional Lambert-W threshold inverse is correct, including
its error scale and integer-threshold interpretation. No substantive
mathematical gap or repair was identified.

One non-blocking wording clarification was identified and has been fixed
in the final pinned source: the original sentence following the inverse
could be read as denying the implied relative inverse asymptotic
nu(y)/N(log y) -> 1. The replacement explicitly limits the unresolved
multiplicative equivalent to a_n and disclaims unit-level rounding and an
all-orders inverse. Exact byte substitution reproduces the original SHA,
certifying that this is the only change from the initially reviewed source.
No issue remains open in the mathematical scope of this audit.

## Pinned inputs

Integrated article:

- `/workspace/shared/oeis-a202058-report/a202058-report.tex`
- Final SHA-256 `8d7bb13a64982e1479996719882d9f188e00899108d4f27e44b42076e1687e1f`
- A byte-identical copy is `a202058-report-reviewed.tex` in this audit folder.
- Initially reviewed SHA-256
  `54fed03e0bf21542c1d81e88953b248f7124f25ffb9cc69e81aebfbfac4cb80f`.
  The exact original is preserved as `a202058-report-original-reviewed.tex`;
  its SHA was verified after reversing the single approved wording change.

Approved radius source:

- `/workspace/shared/oeis-a202058-research/radius-proof.md`
- SHA-256 `51005a5ccb4c7bbfd0fd94139f6fc61e08ceebfbf307f5e98484e7417755c9c4`
- Independent approval: `/workspace/shared/audit-a202058-radius/audit.md`

Approved full-root source:

- `/workspace/shared/oeis-a202058-research/root-limit-proof.md`
- SHA-256 `14c56e5d26ddc6e6204b782dfb93be231265a43782f1151f854164d7152b0e49`
- Independent approval: `audit.md` and `manifest.json` in this audit folder.

The article and both approved source proofs were read in full. This review
did not edit an author file. The radius review here is a faithful-integration
comparison against the approved proof and its detailed independent audit,
including direct checks of the added explanatory formulas. The full-root
review uses the independent derivations in this folder's preceding audit.

## Faithful integration of the radius proof

The integrated article preserves all necessary ingredients, hypotheses,
constants, directions of inequality, and index shifts:

1. The four compacted children and invariant state space match the approved
   recurrence. The explanation of below-last adjacent exchanges agrees with
   the narrower, valid compaction bijection in the independent radius audit;
   it does not assume arbitrary cardinality-only invariance. The initial
   state still gives T_operator^n 1(x_0)=a_(n+1).
2. The characteristic definitions, rank profile, and residual bound
   C(q)=8(1+q)exp(5q/8) are unchanged. The added frozen-integral verification
   is correct: J'(k)=lambda phi'(k) on each side of s, J is continuous at s,
   and the displayed calculation gives J(0)=lambda phi(0)=lambda.
3. The exact child ranks and their 4/D error, the duplicate-ascent bound
   1/8, the exponential mean-value estimate, and the time-derivative bound
   preserve the approved all-state uniformity. No growing-state restriction
   has been inserted.
4. The chain has generator T_operator-mI and is nonexplosive by the same
   Yule domination. The pathwise holding-time cancellation proves the
   extended Feynman–Kac identity with the correct t^n/n! coefficients.
5. The stopped supersolution uses the process with remaining time t-v,
   giving the correct upper-comparison sign. The finite stopped state set
   includes its finite exit boundary; the source argument still applies.
6. Crucially, the lower comparison retains the later-horizon ratio

       G_-(v,y)/G_+(v+eps,y)
          <= exp(q(t+eps)) exp(-eta m(y)),

   with eta positive uniformly over 0<=v<=t. At exit m=N+1, and the later
   supersolution bounds the remaining exit expectation by

       exp(q(t+eps)) exp(-eta(N+1)) G_+(t+eps,x).

   Thus the vanishing boundary term, not an invalid formal unbounded
   subsolution comparison, supplies the lower bound. The article's explicit
   constant agrees with the independently audited sharper statement.
7. E(q)=O((1+q)^3exp(q/8))=o(exp(p)) is preserved, as are the nonnegative
   semigroup identity, deterministic prefix contribution, divergence at
   T_*+delta, and the exact integral T_*=3 pi^2/8.

## Faithful integration of the full-root and error proof

The integrated argument preserves all the components checked independently
in `audit.md`: uniform growing-state estimates, the exact d'/d identity,
uniform bounded-shift H_q'' limit, Chernoff constant 3/128 for both tails,
real thresholds, probability-mass coefficient extraction, floor control,
N-1 prefix length, a_(N+j) index, injective new-label padding, and the full
n!/j! normalization loss.

The explicit quantitative choice q=(8/13)log n and
epsilon=n^(-4/13)(log n)^2 remains valid. Its central mass exponent has
order n^(1/13)(log n)^5, dominating the O(n^(1/13)(log n)^3) barrier error.
The prefix length N is o(epsilon n), and the floor loss M is also
o(epsilon n). The lower logarithmic error is
O(n^(9/13)(log n)^3); the upper error is O(n^(9/13)log n).

For a useful explicit justification of the lower normalization sign, which
is implicit in the article's repeated argument, j<=n and 0<t(q)<=T with
T>1 imply t(q)^j<=T^n. Thus -j log t(q)>=-n log T exactly, and this term
introduces no additional negative quantitative error.

## Independent proof of the Lambert-W corollary

Let alpha=9/13, G(x)=x^alpha(log x)^3, and

    f(x)=x log(x/(eT)).

Stirling's formula and the proved coarse error give constants B and n_0
such that for integers n>=n_0,

    |log a_n-f(n)| <= B G(n).

The O(log n) Stirling term is absorbed because G(n)/log n tends to infinity.
For L=log y>0, put w=W_0(L/(eT)) and N=L/w. Since w exp(w)=L/(eT),

    N=eT exp(w),   log(N/(eT))=w,   f(N)=Nw=L.

This is the unique positive solution for L>0: f is nonpositive on
(0,eT], and strictly increasing on [eT,infinity). In particular N tends
to infinity as y tends to infinity.

Define H=N^alpha(log N)^2. Then H=o(N) and G(N)=H log N. For any fixed
C>0 let

    n_-=floor(N-C H),   n_+=ceil(N+C H).

For sufficiently large N, both integers exceed n_0 and lie in [N/2,2N].
Uniformly over the entire interval [n_-,n_+],

    f'(x)=log(x/T)=(1+o(1))log N,
    G(x)=(1+o(1))G(N).

Choose N sufficiently large that f'(x)>=(1/2)log N and G(x)<=2G(N)
there. The mean-value theorem and outward integer rounding give

    f(n_+) >= L+(C/2)G(N),
    f(n_-) <= L-(C/2)G(N).

Taking any fixed C>4B yields strict inequalities

    log a_(n_-) < L < log a_(n_+).

The padding injection already proved in the article makes a_n
nondecreasing. It also follows from the asymptotics that a_n tends to
infinity, so the threshold nu(y)=min{n>=0:a_n>=y} is well-defined. The
two integer envelopes give

    n_- < nu(y) <= n_+,
    |nu(y)-N| <= C H+1 = O(H).

This proves exactly

    nu(y)=L/W_0(L/(eT))
           +O(N(L)^(9/13)(log N(L))^2).

No smooth interpolation of a_n, monotonicity of a_n/n!, coefficient-ratio
limit, or exact integer-rounding assertion is needed. The formula does
imply nu(y)~N(log y), but does not locate the threshold to within one unit.

## Scope limitations

This mathematical integration audit does not independently replay the
finite diagnostic scripts, certify visual PDF layout, or establish novelty
against the complete literature. The author separately reported a clean
script replay and all-page visual inspection. Neither report is used here
as proof evidence. The manuscript's cautions about unresolved ratio limits,
prefactors, multiplicative equivalents for a_n, and all-orders expansions
are otherwise faithful to what the proof establishes.
