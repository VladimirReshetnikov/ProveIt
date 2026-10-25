# Independent mathematical review of the affine-certificate composition

Prepared with AI assistance, 25 October 2026.

## Objects reviewed and scope

I reviewed the ordinary arithmetic arguments in
`research_direct/AFFINE_HORIZON_PROOF.md`, the affine-radix proof from the
parallel reviewer, the original Factorial-Free Binomial CRT report, and
the orientation-first and strict-budget proofs retained by that parent.
The new selector-offset argument is proved separately in
`alternative_selector/LINEAR_SELECTOR_PROOF.md`.

The reviewed complete front is:

    R=F,
    y=F(2v+1),
    q=4z+1,
    H=2+C+sum(A_j),
    B*h_B=C+F+1,
    q=(BH)^x,
    x=F+1+(y+1)u_0,
    x=1+[1+(t+1)y]u_t.

Either horizon/growth scheme is valid:

    A: t=16h, d=t+2, F=d^t;
    B: t=8h, d=2(t+1), F=d^t.

All displayed variable powers are semantics of existing quadratic Pell
requests. Every underlying unknown is unrestricted integral. The semantic
anchor index is denoted h_* below, to distinguish it from the free horizon
parameter h and the radix multiplier H.

## Finding

No mathematical gap was found in this composition. Its soundness order is
acyclic and its completeness choices are compatible. In particular, the
old assumption t>=16 and the old lower bound W>=258 are not being used
silently to prove themselves after the square horizon is removed.

This review concerns ordinary mathematical arguments formalizable in ZFC.
It does not certify a fresh Lean/Rocq build or an encoded object-language
ZFC derivation. Exact literal source mutations, the complete eighteen-power
interface, the final coordinate maps and every final quartic coefficient
require the separate finite artifact audit. The C222/ZF/ZFC refutation
calibration remains the named inherited logical dependency.

## 1. Frame and orientation audit

The actual frame is W=2+sum(atom^2). It contains both q and q+1, the
semantic anchor index h_*, and every requested principal index k_i.
Thus q=4z+1 gives q^2+(q+1)^2>=5 and W>=7 without any positivity premise.
Also h_*^2<W and k_i^2<W.

The odd frame norm classifies |A| as X_j(W+1), where the nonzero Pell
ordinate is W(2a+1). Reduction modulo W forces W|j; consequently j>=W
and |A|>=X_W(W+1)>W^W. For W>=7, W^W-1>4W^3, so |A-1|>4W^3.
No step here requires the discarded threshold258.

The exceptional |C|=1 anchor branch is handled first. Its squared cap
forces h_*=0 and all other principal ordinates to vanish. The anchor
has classified index1 and the others index0, so every j_i^2<W, but its
ordinate-orientation error is1. The small-error argument below therefore
contradicts that branch. Once |C|>1, the inherited signed-anchor comparison
excludes h_*=0 and makes the anchor's classified index |h_*|; every other
classified index j_i is smaller. Again j_i^2<W for every pair. The small coordinate residues satisfy

    (s_i-1)^2 <= 4,
    (r_i-k_i)^2 <= 2j_i^2+2k_i^2 < 4W.

For at most15 pairs, their nonnegative pooled residue sum E obeys

    E < 60(W+1) < 4W^3 < |A-1|.

The middle inequality holds at W=7, and W^3/(W+1) increases for W>0.
Divisibility therefore forces E=0, proving both coordinate orientations.
The actual source has14 pairs, so the conservative15-pair bound is valid.

The power-modulus estimates also survive W>=7. For any required base
|n|>=2, all atoms have absolute value below W, and

    |2An-n^2-1| > 4W^W-W^2-1 > W^W+W.

For a nonnegative index k<W, the relevant difference is below that
modulus. For a negative index -j, j<W, the integer error |m*n^j-1|
is less than W^W+1, also below the modulus. Thus negative indices are
excluded exactly as in the parent. The exceptional zero/unit bases are
not invoked prematurely.

## 2. Horizon audit

In both schemes d=16h+2, so |d|>=2 for all integer h, even before t has
a sign. The now oriented request F=d^t forces t>=0 and gives its exact
power. If t=0, then F=1 and y=2v+1 is odd. The two endpoint rows reduce to

    x=2+(y+1)u_0,       x=1+(y+1)u_t.

They imply 1=(y+1)(u_t-u_0), impossible because y+1 is even. This includes
y=-1; there is no division by a zero endpoint modulus. Hence t>0,
so t>=16 in scheme A and t>=8 in scheme B.

All later growth premises now follow. Scheme A has F>=18^16>2^32;
scheme B has F>=18^8=11,019,960,576>2^32. Both satisfy F>(t+1)^t,
F>=7, F>2^22, and F>lcm(1,...,t)^2. For the latter use
lcm(1,...,t)<=4^(t-1) and the fact that the respective growth base is
at least18. In both schemes d is even, so v_2(F)>=t.

I checked the explicit occurrences of the old bound16 in the factorial-
free report. They supported the initial frame/growth conclusions, rather
than a separate proof-calculus theorem requiring t>=16. The other numeric
requirements are F>=7, F>2^22, x>2^32, t>=2, (t-1)F>t, and the range
indices at most x. The new bounds imply all of them in both schemes.

## 3. Radix and beta sign audit

The numerator base q+1=4z+2 has absolute value at least2. Its requests
therefore make every actual independent representative nonnegative and
H>=2. The raw index row has positive right side C+F+1; hence B!=0 and
|BH|>=2. The self-radix request gives x>=0 and q=(BH)^x.

At this point y may still be negative. Nevertheless y=F(2v+1) gives
|y|>=F>1, and therefore |1+(t+1)y|>1. The final endpoint excludes x=0.
Thus x>0 and |q|>=2. Only now use the denominator request at base q and
index y+1 to infer y>=-1. A negative y would be at most -F<-1, impossible.
Consequently y>=F. The first endpoint then gives u_0>=0 and x>=F+1;
the final endpoint gives u_t>=1 and x>=2+(t+1)y.

No q>0 assumption occurs in this argument. In particular q=1, algebraically
permitted by q=4z+1 alone, is excluded by the self-radix power before the
base-q request is used. The forbidden numerator base q+1=0 never occurs.

## 4. First digit and selector audit

Put Q=|q| and n=F+t. From x>=2+(t+1)F,

    binom(n,j) <= 2^(t(F-1))  (0<=j<=t),
    Q >= 2^((t+1)F+2),
    max_j binom(n,j)/(Q-1) < 2^(-F-t-1) < 1/32.

The signed low binomial polynomial has absolute value below Q^t/32.
The normalized remainder budget bounds its proposed integer remainder
by Q^t/2. Their difference is divisible by q^t and has smaller absolute
value, hence vanishes. The resulting digit congruence has |B|<Q/2 and
true digit below Q/32, forcing B=binom(F+t,t)>0. Only now does
q=(BH)^x imply q>0. The remaining positive-radix arguments are legitimate.

The replacement R=F satisfies the complete generalized CRT theorem,
including both prime-power coverage directions. F being a square was
never an assumption of that theorem. The later local-majorant bound uses
2+t+x+y+F<2x and x>2^32, both already recovered. The y=F boundary must be
excluded by the inherited zero-accumulator propagation argument, which
continues to apply without a squared beta multiplier.

## 5. Completeness audit

A sufficiently large positive multiple of16 or8 can be chosen after
expanding the refutation to a finite proof tree and before the large
arithmetic witnesses. Truth padding reaches that cofinal horizon. Since
d is even, v_2(F)>=t>v_2(t!). An arbitrarily large odd multiplier 2v+1
supplies every missing odd prime valuation; hence y can be an even
multiple of t!, larger than every accumulator. The usual beta moduli
are pairwise coprime and odd, and their CRT class admits an arbitrarily
large even code x.

For B=binom(F+t,t), v_2(F+i)=v_2(i) for1<=i<=t proves B odd. Thus the
independent representative CRT classes modulo N^2=B^(2x) have free
parity. The parent's choice of odd dominant a and the other representatives
even makes H odd and the semantic anchor even, with the same dominance
bound. No additional congruence is imposed on those representatives.

The actual q=(BH)^x is an odd square because x is even. Therefore q=1
modulo4, and z=(q-1)/4 is integral. All new affine source rows are met.
The existing constructive Pell and common-remainder completions then
supply the remaining witnesses. This is an existence equivalence through
finite-refutation semantics, not a bijection between arbitrary old and new
source zero sets.

## Items that the final release should check literally

- The frame still contains the actual new d, t, q, q+1 and every output
  and requested index; square atom bounds are needed before sign recovery.
- The full orientation pool includes both coordinates of the semantic
  anchor, and every principal pair.
- The d,t,F request and the q,y+1 request remain among the18 actual powers.
- R=F is substituted in every former R position, including n=R+t and the
  raw index congruence, not only in a prose summary.
- The affine horizon is t0=t-16 in the source: t0=16h-16 or8h-16.
- The first beta endpoint remains F+1, not a translation-confused F.
- The full retained logical-calibration/proof closure is packaged or
  explicitly pinned; no consistency assumption is used to choose constants.
