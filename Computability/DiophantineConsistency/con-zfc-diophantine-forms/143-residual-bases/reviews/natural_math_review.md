# Independent mathematical review: shift-free natural quartics, Round 18

## Verdict and scope

**Approved as an ordinary mathematical reduction on the explicitly inherited
indexed-Pell and numerical C222/ZF/ZFC-calibration boundary.** I found no
soundness, completeness, zero-boundary, or circularity defect in the new
shift-free descending-factorial construction. The full new `natural/PROOF.md`
and the relevant incoming descending, cofinal-anchor, consecutive-coordinate,
CRT, Horn-flow, and calculus proofs were read. The new semantic graph and all
coefficients were also checked independently; numerical tests were not used
as evidence for the unbounded mathematical statements.

The initially reviewed contraction has 229 natural coordinates, 179 residuals,
degree 4, 6,596 monomials, and coefficient height 83,879,378. The subsequently
reviewed 42 elementary row shears preserve its zero set and yield 229 natural
coordinates, 179 residuals, degree 4, 5,607 monomials, and height 65,892,965.
Two 228-coordinate contraction companions use the same raw semantic graph.
The 335-coordinate / 285-row raw graph has six exact powers, eleven modular
requests, thirteen nonanchor seeds, **22** actual distinct frame atoms, and
frame offset 15.

No new end-to-end proof-assistant build or closed kernel theorem was checked.
In particular this review does not turn the inherited ordinary logical
calibration into a new formal endpoint. This all-natural branch does not
inherit the unrelated source131 signed-representative/compressed-sign
obligation discussed in the baseline audit.

## 1. Exact source delta and inheritance

A recursive comparison against incoming Cofinal Round17's
`architecture/portable/source` finds exactly two modified files:

* `custom/build_modular_factorial.py`: the descending, unshifted factorial
  and shared CRT-product certificate;
* `custom/build_strict_budget.py`: the reciprocal-index row changes from
  `C+F²+1=Bq_C` to `C+1=F²+Bq_C`.

`build.py` differs from incoming `build_strict_anchor.py` only in the chosen
factorial method and the descriptive semantic tag. Thus the actual Cantor
constructors, nine axiom/guard branches, local source, source/label majorants,
strict beta ranges, full anchor, and frame/denominator implementation are not
silently changed. The input numerical source and arithmetic compiler are
byte-identical inherited files. The full semantic checker verifies the
emitted cap, frame, power and modular interfaces rather than relying on this
textual comparison alone.

The active incoming closure map explicitly identifies
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation` as inherited ordinary
calibration, not a newly kernel-checked dependency closure. The retained
calculus text gives the literal Cantor formulas and the Horn-flow argument;
the new construction leaves them unchanged.

## 2. Bootstrap: no factorial or binomial assumed early

The independent natural variable `n` obeys `n+1=F²`. This row is deliberately
not a globally nonnegative definitional substitution `n=F²-1`. The retained
natural modulus variable obeys

    T_n+n²+1=2An.

If `n=0`, the left side is positive and the right side zero. Hence `n>=1`;
integrality of the natural square then gives `F>=2` and `n>=3`. This argument
uses neither authenticated Pell indices nor the proposed power value.

The frame and full semantic anchor can therefore be interpreted first. The
other exact-power bases are independently positive from their own modulus
rows, and all nominal exponents are positive: `t>=12`, `x>=F+1>=3`, and
`y+1>=4`. Every modular upper index is positive as well. Each consecutive
pair has an output incidence with a nonnegative right side and base below
`A`, giving its positive Pell orientation before index authentication.

After the exact powers are recovered, `V=n^t`. The floor rows give
`B=r+s+1>=1` and `V=BF+r<B(F+1)`. Since `F>=2`,
`n=F²-1>=F+1`; already `n²>F(F+1)`, so `V>F(F+1)` and `B>F`.
Consequently

    V < B(F+1) <= B² <= B^x=N <= (NS)^x=q.

For every `0<=j<=t`, `binom(n,j)<=n^j<=n^t=V<q` (the value is zero
when `j>n`). This is the first exact-digit carry bound and does not use
`B=binom(n,t)` or `F=t!`.

There is also no hidden root-modulus circularity. The raw endpoints give
`x>=3`, `y>=3`, and `x=1+[1+(t+1)y]u_t`; hence `u_t>=1` and
`x>=2+(t+1)y>max(t+1,y+1)` before factorial decoding. Therefore
`M=Nq^x` is already a multiple of every required digit modulus. I requested
that the draft place this elementary observation before the first digit
interpretation for clarity; it was not a mathematical gap.

The exact digit now identifies `B=binom(n,t)>0`, so `n>=t`. The floor
rows genuinely express `F=floor(n^t/binom(n,t))`.

## 3. Descending fixed point and CRT boundaries

Let `T=t!`, `U=t(t-1)/2`. For `t>=3` and `n=F²-1>=t`,

    H=n^t/binom(n,t)=T product_(j<t)(1-j/n)^(-1) >= T.

The proposed floor identity implies `F>=T`. The elementary induction
`T-1>U` gives `n>=T²-1>(T+1)U`; therefore

    T <= H <= Tn/(n-U) = T+TU/(n-U) < T+1.

Its floor is `T`; thus `F=T`. Conversely the same bound at `F=T`
constructs the natural remainder and slack. The excluded cases `F=0,1`,
`B=0`, and `n<t` are excluded by polynomial or already-decoded conditions,
not omitted from the proof.

For `d_i=F²/i-1`, each `i|F`, so `d_i` is an integer and is `-1`
modulo `F`; it is greater than one. Every prime divisor is greater than
`t`. A common prime divisor of `d_i,d_j` would divide `j-i`, impossible
for distinct indices. Their product is exactly `binom(F²-1,t)=B`.
The changed row `C=n+Bq_C` has the correct sign: modulo `d_i`, it gives
`C=i-1`. In completeness, `B>n` follows from
`3<=t<=n-2` and `binom(n,t)>=binom(n,2)>n`. Every positive representative
of `n mod B` is therefore at least `n`, so `q_C>=0`. This is an actual
natural-quotient argument, not a signed quotient hidden in the notation.

## 4. Cap, strict budget, and cofinal completeness

The unchanged lower-scale norm gives `A>=(W+1)^W`, independently of the
proposed powers. The one-row cap

    Y_H = H + sum_i(Y_i-k_i)² + (A-1)Q

first supplies the full anchor certificate's omitted `H<=Y_H` premise.
With `2<=H<W`, a putative actual seed index `j_i>=H` makes one error
square exceed `Y_H`; hence all actual indices are below `H<W`.
Modulo `A-1`, the remaining sum of small squares is a multiple of `A-1`
and is less than `W³<A-1`, so each index is the requested one. No premise
`k_i<H` was incorrectly assumed in this soundness argument.

After `F=t!`, the unchanged endpoints yield `R=2+t+x+y+F<2x` and
`x>2^32`; the retained literal exponent `E=2^23` gives `R^E<2^x`.
The label exponent is `ell=2^22`, with `ell(t+1)<F<x`.
Every positive independent representative is below the actual sum `S`,
so all required ordinary binomial coefficients are below `S^x<q`; the
label coefficients are bounded by `S^(ell(t+1))<S^x`. Enlarging one
representative does not invalidate a bound tied to the *actual* sum.
The equality case `k=x` is harmless in the precision estimate because
`v_p(k!)<=k-1<=x-1`.

Completeness first pads a finite refutation and chooses its beta data,
then `F,n,B,N`. CRT is performed modulo `d_i^(2x)`, not merely
`d_i^x`; the falling-factorial valuation minus the factorial loss is
at least `xm`. This is the valid direction of range completeness and
not the false converse of the prime-power range lemma.

Choose the nine positive representatives in `(0,N²]` and increase only
`Aa` by `N²`. Every independent representative is at most `2N²`.
The fixed remaining nominal indices `t,y+1,x,n` are below
`x²+x<2^x<=N`. Thus the greatest nonanchor index is at most `2N²`,
whereas `J>=2(Aa+N²)²>2N^4>4N²`. The cap's completeness hypothesis
is satisfied. Only afterwards are `S,q`, denominators, frame and Pell
witnesses chosen. Since `N|q`, the common-root linear congruence is
soluble (the only possible gcd obstruction is 2, which divides its
right side). Arbitrarily large choices of `A` provide natural scale
and root quotients. There is no cyclic witness selection.

The decoded local source, beta consistency and pairwise-coprime Horn
weights then give a finite C222 refutation by the retained finite-flow
argument. Conversely a finite proof tree supplies the padded local data.
This is the same ordinary calibration, not an appeal to consistency.

## 5. Exact finite verification performed

* Rebuilt the 229-variable precursor from inspected `build.py` into
  `review/natural_rebuild229`; all ten generated JSON objects agree with
  `natural/unshifted32` (JSON equality, allowing whitespace).
* Replayed all 613 defining gates, 392 nonnegative affine restorations,
  dependency closure, 285 raw rows, and 4,606 raw SOS coefficients with
  `check_affine_export.py`. Five distinct corruptions were rejected.
* Adapted the independent Round17 semantic checker without importing any
  producer module. The adaptation checks the new square-minus-one row,
  natural base modulus, floor and remainder rows, single merged binomial,
  literal horizon, and reversed index row before propagating the proved
  positivity. It checks all seeds, full anchor, exact frame, six powers,
  eleven modular rows, actual Cantor lower bound, source normalization,
  all monic natural restorations, and all quartic coefficients.
* Normal and `python -O` semantic checks agree. Fourteen corruptions are
  rejected, including five targeted at the new descending rows. The
  229-variable precursor has 106 checked eliminations, including two
  restorations with negative expanded coefficients whose positive
  rational-square certificates are checked exactly.

The portable audit is `natural/audit/check_semantic.py`. Main receipts
are `natural/audit/SEMANTIC_REVIEW229.json`,
`review/natural_affine_review.json`, `review/natural_rebuild_compare.json`,
and the semantic normal/optimized receipts. The checker supports a shared
`--source` directory and separate immediate contraction endpoints. A
row-sheared endpoint must be checked by chaining the contraction precursor
with its row certificate, not by pretending it is the direct contraction.

## 6. Independent row-shear review

I read `check_row_basis.py` and the complete 42-operation certificate.
Each operation is `R_i <- R_i+k R_j` with distinct rows and integer `k`;
its inverse is the opposite shear. Coordinates and their natural domain
are unchanged. Thus the simultaneous residual zero sets are identical,
and over the natural numbers each SOS is zero exactly when every residual
is zero. **The two SOS polynomials need not be identical**; zero-set
equivalence is the correct claim.

In addition to running the independent forward/reverse row checker in
normal and optimized Python (five corruptions rejected), I separately
formed the full integer transformation matrix `T` and reverse matrix `U`.
Every target residual equals its stated linear combination of source
residuals, and `UT=I` exactly. A separate dictionary expansion gives
5,607 monomials, exact degree 4, height 65,892,965. The receipts are
`review/natural_row_shear_review.json` and
`review/natural_row_matrix_review.json`.

One artifact-only issue was reported immediately: the experimental row
certificate's embedded `equation.metrics` retained the precursor's
6,596/83,879,378 values, although its outer metrics and rows correctly gave
5,607/65,892,965. The release must refresh the embedded metrics and literal
expanded polynomial. This does not affect the proved row equivalence.

## Evidence boundary

The exact scripts establish finite syntax, identities, restorations and
coefficients. The unbounded argument above establishes the new arithmetic
semantics. The indexed-Pell theorem and the explicitly named C222/ZF/ZFC
calibration remain inherited ordinary mathematical dependencies. No finite
search proves unsolvability, no consistency assumption is used, and no
worldwide minimality or new kernel closure is asserted.

## Final release checks

The artifact-only metrics issue above is **resolved** in
`natural/release/balanced229`: its embedded metrics are 5,607 monomials and
height 65,892,965; independently expanding its residuals agrees with every
literal expanded coefficient, and its rows agree with the released
row-basis certificate. See `natural_release_row_review.json`.

Both immediate 228-variable companions also pass the complete semantic,
normalization, contraction and coefficient audit normally and under `-O`,
with fourteen rejected corruptions each: `low_height228` is 228 variables,
178 rows, 9,522 monomials, height 560,804,902; `sparse228` is 228 variables,
178 rows, 7,512 monomials, height 2,445,412,949,744. Their receipt is
`natural/audit/SEMANTIC_REVIEW228.json`. These tradeoffs do not dominate the
229-variable balanced equation in all metrics.
