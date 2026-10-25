# Independent ordinary-mathematics review: compact denominator family

Reviewer: separate baseline/audit agent, 25 October 2026. Scope: new `round18/compact/PROOF.md`, literal construction in `build.py`, the six emitted circuit definitions, and the relevant retained ordinary source interfaces. This is a read-only mathematical review, not an execution receipt or external peer review.

## Verdict

**The six repaired charts have a valid ordinary zero-existence reduction under their stated inherited native/refutation calibration.** The four useful operation/degree tradeoffs are **77/626, 78/464, 79/460, 80/384**, all in ten strictly positive integers with the same whole indexed BFS943 tuple. The 78/622 and 79/518 variants are dominated controls, not additional Pareto claims.

The earlier exploratory **81/410 and 82/304 linear-normalization candidates are rejected**. Their modulus argument does not establish the required first index. Their finite degree/count plausibility did not rescue their soundness proof. They were removed from the final six-chart family and the failure is expressly retained in the new proof.

No proof of consistency, universal nonvanishing, global optimality or new end-to-end formal-kernel endpoint is established here. No supplied executable was run by this reviewer. Fresh finite circuit/byte/count/leading-form/corruption checks belong to the parent's separate audit.

## Reviewed mathematical boundaries

The new proof inherits and explicitly credits:

- `provenance/staged_denominator.md`: the scale-one Pell construction and recovery of a first index from a known divisor before full denominator recovery;
- `provenance/unshift.md`, `unshift_general.md`: sign-free auxiliary transport, including both third-index auxiliary signs;
- `provenance/universal_pell.tex`: all-index folding, normalized strong rank, signed auxiliary index, projection and constructive auxiliary completeness;
- `provenance/uniform_ratio.md`: the ratio estimate for every scale at least one, hence legitimately scale one;
- retained source/native/half-binomial/calibration texts, with the entire actual four-port tuple rather than arbitrary numerals satisfying merely its port box.

Changing the transport denominator does **not** change the first Pell norm: throughout, `v=XY²` and `E=1+v(v+1)k²`. The three denominator choices are:

| Chart | Y | D | Rational retained padding σ |
|---|---|---|---|
| XY | q³s | XY | 0 |
| q4 | q³s | q⁴ | 0 |
| partial | q²s | q³Y=q⁵s | s/q=Y/q³ |

The partial chart has the exact identity `Dσ=Y²`. Accordingly its literal numerator differs by `H[h(Y²-e)-DB]`, not by an unproved integral padding substitution. All three yield exactly `z=n+κ+σ-(1+hL)B/h-e/D` over rational numbers before any integrality is established.

## 1. Root extraction does not borrow later sign or divisibility conclusions

For positive inputs `q>=32`, `X>=q`, `Y>=q`, `c>k>=2`, and `M=hDH>0`. The identities

`Fsq=(1+2a)²`, `Q=4Δ²U²G`, `gcd(E,1+a)=1`

do not require any native decoding or a positive sign for b or V. Since G divides Q, the integer factors `Q-1` and `QV²-1` are both coprime to G. Their rational equality with `G` times a square forces every valuation of G even; **coprimality of M and G is not needed**. Hence `E=τ²`, `1+a=f0²`, `G=g²` and the adjacent Pell equation follows.

The given rational adjacent-Pell descent is valid: a reduced denominator m has `m² | Q-1`; the displayed transformation has an integer first coordinate, preserves the reduced denominator of the second, and decreases the nonzero absolute first coordinate strictly when it exceeds one. Reflection only changes signs. At first coordinate one the second is one, proving integrality. Thus z is a signed integer `±gy` before transport or rank recovery.

The doubled strong pair has exactly `f²-ΔI²=1`, `c²|I`, `Q=(ΔI)²` and fixed-minus residue `V=-c mod f`. Signed folding permits either sign of V. The first index cannot be one, giving

`c>kY>8XY³>=8q⁴`.

This supplies `c>X`, positive κ, and eventually the required `c>2R`; none was inferred from C>0 prematurely.

## 2. The unshifted sign proof is valid at scale one

The proof correctly avoids applying an old positive-domain theorem to `T-alpha`, which need not be positive.

- b=0 would make an integer square differ from c² by a number strictly between zero and one. Thus b≠0, V has b's sign, and `|V|>|b|`.
- The exact a/G identity gives `a>g`; the unconditional strong sizes give `Fsq-c>3a>3g`. Therefore `gy<V²/2` without positive b or V.
- For the bV weight, the scale-one p=3 exclusion is genuine, not inherited from a proof requiring `mu>=1025`. If p=3 and the first index is at least three, Pell growth contradicts the explicit bound on c. With index two, the expanded eta identity forces `2Y-X` into {1,2}; since q divides both X and Y this is impossible. Thus p>=5.
- Both possible signed third auxiliary branches are excluded separately by `Fsq(b-4Δ)=c-c3` and `Fsq(b+4Δ)=c+c3`, whose positive right sides lie strictly below Fsq. It follows that `|b|>4g` and `gy<L/2` for `L=bV`.
- The bound `e<b` uses only `cT-k+1>0`. It is one-sided and does not assume rho nonnegative. Since D>2 and σ>=0, B<=-1 would imply a negative actual input n. Hence B>=0 and C>0.

Only after this contradiction does the proof use `3q<R<q⁴-2`. It then restores b,V positive and the actual rank p=R. The signed rank hypotheses and fixed-minus residues remain intact; no b>c claim is needed. In particular T=1 remains allowed.

## 3. First-index recovery: the decisive denominator check

The first norm gives `k=2n0 mod 4XY²`. The strict base comparison gives `1<=n0<R` after rank p=R. Consequently the desired error satisfies `|2n0-R-1|<R<q⁴`.

For the two cubic charts, integrality of z implies `D | hHe`. Because q⁴ divides D and `gcd(q,hH)=1`, q⁴ divides e. Also q⁷ divides XY², so the recurrence legitimately supplies `q⁴ | 2n0-R-1`.

For the repaired partial chart, multiplying the rational carrier by qhH clears the other fractions and gives `D | qhHe`. Here q⁵ divides D; coprimality therefore again gives q⁴|e. Crucially, **q⁵ also divides XY²** for `X=qw,Y=q²s`. Thus the same modulus applies to the recurrence. The bounded error is zero.

After obtaining `2n0=R+1`, return to the **full** recurrence to obtain `4XY² | e`. Every chosen denominator divides that modulus; in the partial chart

`4XY²/(q³Y)=4ws`.

This proves rho integral without asserting the false general premise `gcd(Y,h)=1`.

### Rejected predecessor and disposition

The discarded chart had `X=qw,Y=qs,D=q⁶,σ=s/q²`. Its carrier could give q⁴|e, but `4XY²=4q³ws²` is not generally divisible by q⁴. It therefore yields only a q³ index-error congruence, insufficient against `R<q⁴`. The author flagged this while writing the proof and this independent review confirmed the defect. An earlier preliminary endorsement of its degree arithmetic did **not** establish soundness. The repaired Y=q²s chart increases the recurrence modulus and fixes exactly this gap. The rejected 81/410 and 82/304 counts must never appear as achieved results.

## 4. Projection and the final native fractions remain noncircular

The scale-one uniform ratio estimate, now at the recovered index, implies `Y>X^r/3` and `H>X^(r+1)`. Integral rho permits clearing denominators in the carrier: `H|hK` in the cubic charts, and `H|qhK` in the partial chart. Both imply the retained weaker `H|q³hK` premise.

The inherited universal projection and **whole-product** size bound force X=2^R; they do not cancel arbitrary factors modulo H. The hypothesis `r>=48` follows from R>3q and q>=32. κ is now integral.

For the partial chart, integrality of `s/q-WB/h` and coprimality `(q,h)=1` first imply q|s and h|WB. Since W=1 mod h, h|B. Thus q³|Y and t=B/h>=0 are restored before the inherited fixed-minus parity and half-binomial/native decoding interfaces are used. This order is essential and is correct in the repaired proof.

## 5. Completeness is a positive canonical reconstruction

The retained refutation calibration supplies canonical X=2^R, q³|Y, R=3 mod4, R>3q and nonnegative integral t. Choosing s=Y/q³ or Y/q² respectively is legitimate. The scale-one ratio and rounding bounds supply positive eta,zeta. Full recurrence divisibility supplies integral nonnegative rho.

The fresh seed is chosen at a Pell matrix period modulo c²τ, so i=I0/(c²τ)>0 and the doubled pair agrees with all literal definitions. The auxiliary-completeness theorem supplies a positive integral **raw** T; no subtraction of alpha occurs.

The partial padding is now integral because σ=Y/q³. Its extra positivity cost is explicitly handled: σ<Y<Xc and κ<Xc, whereas `f0>(A-1)I0>2Xc`, hence `g>κ+σ`. Therefore `n=gy+Wt+rho-κ-σ` is a positive integer and its exact carrier is z=gy. This closes the new existential direction with all ten independent coordinates positive.

## 6. Independent exact global leading forms

I derived the entire highest forms symbolically from the defining expressions, independently of the finite checker. Write `q0=βJ`, `k0=eta+zeta`, `C0=q0-F-alpha`. The six forms are:

```text
xy_v2:      2^14 q0^378 w^48 s^110 i^20 k0^64 T^4 C0²
xy_bv:     -2^10 q0^284 w^36 s^82  i^14 k0^46 T²
q4_v2:      2^14 q0^378 w^46 s^108 i^20 k0^64 T^4 C0²
q4_bv:     -2^10 q0^284 w^34 s^80  i^14 k0^46 T²
partial_v2: 2^14 q0^272 w^46 s^110 i^20 k0^64 T^4 C0²
partial_bv:-2^10 q0^206 w^34 s^82  i^14 k0^46 T²
```

Their degrees are respectively 626,464,622,460,518,384. All are nonzero at the actual positive β. For the squared weight, `QZ²` is uniquely top-degree; for bV, `-QM²GV²` is uniquely top-degree, so no neglected equal-degree cancellation occurs.

As an independent partial-chart check, the complete leading building blocks are `M0=4q0^9ws²`, `Q0=4q0^54w^10s^22i⁴k0^12`, `G0=q0^34w⁶s^14i²k0⁸`, `V0=4q0^50w⁸s^21i⁴k0^13T`. The field degrees Q102,M12,G64,V97 give the bV degree 384 directly. This is an unbounded polynomial identity/degree argument, not a sampled-ray check.

## 7. Artifact and editorial checks

The reviewed builder imports only standard-library modules and transforms frozen JSON data; it does not execute copied parent code. Its revised partial construction changes Y's operand to q², adds `D=q³Y`, and uses `h(Y²-e)-DB` with the correct plus sign in Z. The four cubic transformations agree with the formulas. Operation changes relative to the complete parents are syntactically consistent with the claimed counts; a fresh independent count/liveness/row-cut replay remains outside this review.

Two final editorial corrections were requested: mark **both** q4_v2 and partial_v2 as dominated controls, and print the two partial leading forms locally in the ordinary proof instead of referring only to the checker/report. Neither changes the repaired polynomial theorem, but both matter to an accurate standalone deliverable.

The copied `provenance/SOURCE_PINS.json` initially retained historical `proof_sources/` and license paths. It needs to be labeled as a historical ledger and accompanied by a current local source map; a historical path must not masquerade as an active runnable closure. This is a packaging/provenance issue, not a reason to run the inherited programs. Parent finite/package review should verify the final binding and inherited notices.
