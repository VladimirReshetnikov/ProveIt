# Independent review: signed affine horizons and compressed frames

Reviewer: separate round23 intake/audit task, 26 October 2026 UTC. This is AI-assisted internal review, not external refereeing.

## Verdict and scope

The ordinary theorem in `package/PROOF.md` (also `NEW_THEOREMS.md`) is accepted for m=16 and m=4, including the optional compressed affine frame and difference orientation. The source remains the explicitly pinned incoming PellGrowth210 system and its named C222/ZF/ZFC calibration. The new reductions preserve existence of integer zeros; the cofinal-source/frame changes are not falsely described as bijections with arbitrary original witnesses. Unit wire insertion, affine elimination and invertible row operations have the stated exact maps.

## Critical sign order

The divisibility row gives |F|>=2^19|t|, F nonzero/even, before a Pell theorem at positive center is used. With t=m(2z+1), m>=4, one has |t+1|>=m−1 and |y|>=|F|. Thus the terminal beta denominator has magnitude at least(m−1)2^19m−1>1. The already authenticated q=D^x at a nonzero even D gives x>=0; the terminal beta row excludes x=0. Only then is |q|>=2 available and the actual retained q^t request (`pow4.output` at `index0`) forces t>=0. Hence t>=m and the standalone positive-center growth proof can be invoked. Negative horizons cannot bypass this order.

## Small-horizon repairs

The old t>=16 threshold is not silently reused at m=4. The explicit constructor inequality works on nonnegative inputs;0 and1 are below t>=4. The exact depth19 majorant L=8^(d−1)t^d is therefore valid. Pell divisibility and valuations yield n>=dt, and (8t)^(dt−1)/L^t=8^(t−1)/t>=1. This much stronger growth implies F>2^64 and F>16^t after sign recovery, supplying the unchanged local polynomial and factorial-free CRT inequalities. The source's initial W>=258 is recovered from the retained F atom, not from the now smaller t².

For completeness, t≡4 modulo2^24 is cofinal. Its valuation2 implies valuation21 of the selected Pell ordinate. The same normalized Pell residue permutation constructs F≡2^21 modulo2^L0 with2^L0>t; t's bit21 vanishes. Thus B=binom(F+t,t) is odd. The prime-support beta-spacing argument does not impose the false stronger requirement t! divides a number of fixed2-adic valuation. CRT representatives and the main shared-Pell center are chosen afterward.

## Compressed frame and orientation

The independent exact ledger confirms34 actual atoms and, for m=4,29 underlying coordinates, frame constant22 and max(|constant|+sum absolute affine coefficients)=13. In particular F remains framed and W>=(2^21)²+22. This gives the new bound |atom|<=13sqrt(W), not the old atom²<W.

The final proof intentionally uses a slightly looser uniform integer budget b=(3m+2)ceil(sqrt(W)), for m∈{4,16}. At W>=2^42 it satisfies b<W,4b+1<=W and b²<=10000W. Hence the negative-index-cleared fixed-base error is <=60b^(4b)<W^(4b+1)<=W^W, while |T|>W^W. This repairs the genuine gap that would arise from reusing the old squared-atom theorem unchanged.

The modified orientation replaces precisely one error square by its difference with the retained t-error. The recorded quadratic delta is exact. The nonnegative reduced residue sum has bound57W²+52<4W³<|A−1|, and the retained t-error recovers the omitted F+t error. The classified-index cap is used before requested-index orientation, in the inherited order. Completeness chooses every framed coordinate before W and then the free Pell center, so the changed frame is cofinally available.

## Independent finite checks

The separate `review/check_selected_independent.py` imports no construction program or its checker. It starts at the exact frozen incoming210 source; reconstructs all semantic horizon/frame/orientation edits; verifies the34-atom ledger, frame constant22, actual affine expressions and maximum L1-plus-constant13; checks every monic growth-factor split; performs the horizon projection into every row; replays every reversible integer row operation; and independently convolves the entire final sum of squares. Every resulting coefficient and coordinate declaration agrees with its literal file. Normal and optimized Python runs pass. The complete binding receipt is `review/SIGNED_SELECTED_INDEPENDENT.json`.

Confirmed FINAL selected profiles:

| Profile | Integer variables | Rows | Exact degree | Collected terms | Exact height |
|---|---:|---:|---:|---:|---:|
| dimension209 |209|149|4|5278|70,368,744,177,664|
| principal210 |210|150|4|5276|16,777,216|
| balanced211 |211|151|4|5401|65,537|
| low212 |212|152|4|18381|5,200|

The final balanced211 uses split exponents[4,8,7] and four row operations; its independently checked equation SHA256 is `f7ff03f3cc6f5dae949a32a430d6840fd7592efbd3f09c4ecebef404945b2eb1`. This supersedes the exploratory[5,7,7] profile of height72,940. Principal210 uses[8,11]; low212 uses[3,5,6,5] and426 row operations. All split exponents sum19, and the checker establishes each literal map, not just this numerical sum.

An earlier separate checker also verified the conservative affine m16 source209/149/degree4/5486terms/height2^50 and the unrefined compressed frame profiles. The final-table checks above include the complete selected split and row-basis endpoints; they do not rely on that earlier partial audit as a substitute.

Neither these finite checks nor the ordinary arithmetic review newly compile the inherited logical development or prove Con(ZFC). They establish the stated proof composition and exact polynomial definitions at the declared boundary.
