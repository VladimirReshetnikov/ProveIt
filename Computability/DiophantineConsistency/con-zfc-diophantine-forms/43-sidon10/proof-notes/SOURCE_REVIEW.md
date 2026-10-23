# Independent B2 source-interface review

**Verdict: the new source construction is mathematically valid**, with the
inequalities below and the authentic shifted quadratic residuals. This is
an independent ordinary mathematical review, not a Lean/Rocq certificate.

A complete derivation is in `BLOCKWISE_QUADRATIC_SOURCE_AUDIT.md`.

## Exact source interface

The 31 source unknowns use the 31 positive members of the 32-element Sidon
set; position zero is reserved for the constant 1 in `(1+g)^2`. The Sidon
condition must cover all 528 unordered pairs **including zero and repeated
entries**. It gives unique positions for every monomial of total degree at
most two. Merely checking pairwise distinct nonzero differences without the
zero and repetition cases would be insufficient.

Let A bound the absolute values of the factorial-weighted coefficients of
all 22 shifted quadratic residuals. In the delivered notation, M=799,
W=2M+1=1599, Q=21W+4M=36775, and h=21W+2M=35177. Put

    D_j(B) = sum_alpha (2-|alpha|)! alpha! r_(j,alpha)
                        B^(2M-alpha.w),
    D(B) = sum_(j=0)^21 B^(jW) D_j(B).

The fifth original residual, `E-X(a-E)`, has shifted constant +1 and is
placed last. Hence the leading coefficient of D is exactly +2, at degree h.
Each lower coefficient is bounded by A, and the block supports do not
overlap. If B-1>A then D(B)>B^h>0. This positivity holds for arbitrary g;
it does not use correct digit encoding or source solvability.

The delivered beta=2^2134940 is a power of four. The stated audit bound
A<2^2134927 implies beta>8192 A. This is more than the sufficient
beta>2 A (31+1)^2=2048 A. With B=beta b^2, that inequality gives

    B/2 > A(1+sum_i z_i)^2

for all source digits 0<=z_i<b.

## Extraction and no-carry test

For c(t)=1+sum_i z_i t^w_i, the coefficient of t^(2M) in c(t)^2D_j(t)
is exactly 2r_j(z). Each product has support in [0,4M]; offset jW places it
in [jW,jW+4M]. These product intervals may overlap, but their target
positions jW+2M do not lie in another product interval: the previous
interval ends at this target minus one, and the next starts at this target
plus one. Thus the targets test all 22 residuals independently. The D_j
intervals themselves have width 2M and remain disjoint; consequently the
coefficient bound A on D remains valid at every position.

For encoded g, the expression

    J/2 = (1+g)^2D(B)+(B/2)sum_(k=0)^Q B^k

has digits e_k strictly between zero and B. The target digit is
B/2+2r_j(z). When b is a power of two, B is also a power of two. Binary
no-carry against `(B/2-1)sum_j B^(jW+2M)` forces every target digit to
equal B/2. Doubling both addends preserves no-carry, so the equivalent
mask on J is `(B-2)sum_j B^(jW+2M)`. Adjacent positions are not required;
the mask acts on disjoint digit blocks. Signs of residual coefficients
are harmless because the B/2 digit bias is strictly larger than their
convolution magnitudes.

## Bounds needed before the Lucas bridge

Assume only f!=0, b=1+3f is a square, and 0<=g<2bB^M. Then b>=4,
B>=2b, and g<N0=B^(M+1). Since g is integral, 1+g<=2bB^M.
Using `|coeff D|<=A`,

    0<J<[(8Ab^2+B)/(B-1)]B^(Q+1)<2B^(Q+1)<N1,
    N1=4B^(Q+1).

The strict middle inequality follows from beta>8192A (in fact beta>8A
with b>=4 suffices). This argument does not assume that g has passed its
digit test, and does not assume b is a power of two.

The low mask M0 has digits B-b at the allowed positive positions and
B-1 elsewhere, including position zero. Thus 0<=M0<N0. The high mask
H0 is below B^(Q+1)<N1. Consequently

    S=g+JN0 and T=M0+H0N0 lie in [0,N0N1).

Because beta is a power of four and b=1 mod3, B=1 mod3 and
N=N0N1=4B^37576=1 mod3. Hence X=(N-1)R is divisible by 3. Also
R=(S+T+1)N+T+1>=N+1>B>=b, so X>=3b and Y=N^2>=max(b,256).
These are the source-interface requirements needed by the ten-integer
Lucas bridge, established before its power-of-two conclusion is used.

## Soundness and completeness

Once b is known to be a power of two, Sun 2021 Lemma 2.4 applied with
cap 2bB^M recovers unique source digits z_i in [0,b) from
`tau_2(g,M0)=0`. The cap condition is b<=2b<=B. The low and high blocks
give

    tau_2(S,T)=0 iff tau_2(g,M0)=0 and tau_2(J,H0)=0.

Sun 2021 Lemma 2.2 (P=p=2) equates this to Y dividing binomial(2X,X),
using the already proved bounds S,T<N. Coefficient extraction then gives
all 22 residual equations. This proves soundness.

For completeness choose an arbitrarily large b=4^k, set f=(b-1)/3,
and encode a fixed nonnegative source zero. The zero is nonzero because
the fifth residual has shifted constant 1. All occupied positions are
positive, so g>=B>=b; the usual digit bound gives g<bB^M. Both no-carry
conditions hold, hence the binomial divisibility follows. The arbitrary
size of b supplies arbitrary lower bounds on f as needed by the bridge.

## Dependencies and claim boundaries

The argument proves a new multi-target quadratic source lemma directly;
Sun's published one-target Lemma 2.6 is not simply invoked with changed
parameters. The subsequent Lucas/interpolation results and ten-integer
finalizer remain mathematical dependencies. The parent residual system's
equivalence to non-consistency remains the inherited K215/compiler theorem.
No source solution is produced or assumed. No consistency statement is
decided. The degree bound and operation count require the separate circuit
audit; they are not consequences of finite no-carry experiments.

Primary text independently inspected:
Zhi-Wei Sun, *Further results on Hilbert's Tenth Problem*, Sci. China Math.
64 (2021), 281-306, arXiv:1704.03504v7, Lemmas 2.2, 2.4, 2.6 and proof of
Theorem 3.1: https://arxiv.org/html/1704.03504v7.

## Additional concrete checks

Independent direct arithmetic on the materialized four coefficient ports gives
maximum weighted-coefficient bit length 2,134,926. In particular A<2^2134927
and beta>8192A hold strictly. All 528 two-element multiset sums of the 32
delivered positions were enumerated and are distinct. These finite checks
confirm the hypotheses of the proof; they do not replace that proof.

## Reproduction command

The finite verifier accepts any unpacked candidate root containing
`generated/source_records.json`, `generated/METRICS.json`, and the four
compressed coefficient payloads under `data/`. Run from any directory:

    python3 check_b2_source_independent.py --candidate /path/to/candidate

Use `--output /path/to/receipt.json` to retain its report. No module imports
from the candidate or from the development workspace are used.
