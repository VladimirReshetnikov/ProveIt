# Fixed-prime separation in twelve unrestricted integers

**The twelve-variable arithmetic component passes ordinary review and complete scoped normal/optimized replays.** Both new forms improve the previously reviewed interpolation tradeoffs at the same whole source34 tuple:

| Domain | Variables | Operations | Exact degree |
|---|---:|---:|---:|
| Integers, rational auxiliary radicand | 12 | **215** | **2,400** |
| Integers, integral auxiliary radicand | 12 | **209** | **2,912** |
| Previous pointwise optimized interpolation | 12 | 239 | 4,832 |
| Previous pointwise optimized compact interpolation | 12 | 215 | 16,000 |
| Previous optimized trace companion | 13 | 184 | 1,072 |

The new twelve-variable forms dominate both earlier twelve-variable points. The thirteen-variable trace retains a different degree/operation/variable tradeoff. The positive13 canonical page and the new twelve-integer forms have different domains and coefficient tuples; there is no automatic PDF replacement or coefficient substitution.

This review covers only `integer12/`. It does not assess or replay the direct1190/1224 quartics or the positive98 supplemental evaluator. The accepted consistency interpretation composes the new arithmetic with the retained ordinary native/compiler/K215 calibration. No new Lean or internal object-ZFC endpoint is claimed; Lean is paused.

## Arrival, provenance and finite checks

The complete arrival is `docs/incoming/ConZFC_Valuation_and_Signed_Certificates_2026-10-23.zip` at commit `3635835b1e96f5810ac55216a58a8ba75a721dab`, SHA256 `11267f89709f1bb10ba1237d29733727d9c41cebd783041419eb0773e6e7f937`. The 302-file,9,748,999-byte original is preserved unchanged under `/tmp/proofs62ff-valuation-signed-review/original/ConZFC_Valuation_and_Signed_Certificates`. Every original member and all299 manifest entries authenticate. The manifest excludes itself and the two final release receipts; the full arrival inventory also pins those receipts.

All93 inherited root-fusion files and the four retained interpolation proof/audit files are byte-identical to the already reviewed arrival. The six actual ports `beta,K0,MC,MF,cone_A,cone_B` have the same 615,883 minimal raw bytes and previous source34 digests. Here `beta=2^1064921−1`, `MF` is already shifted, and the two determinant scales are `2^1113` and `2^666104`.

Two complete scratch copies were used. In **each** Python mode, the four scoped stages pass: regenerate the rational graph; regenerate the integral graph; run the producer-independent front/conjugate-product checks; compare every coefficient of the universal denominator-cleared five-root norm. Both regenerated graphs are byte-identical to their delivered originals. The exact generic norm has20,349 terms, with canonical coefficient digest `2ca48f61e4505f15ed2d935397d08f1a656611fb012f1927cbbd93c08af929dd` in both modes. Each equation also passes72 complete norm comparisons,36 zero-multiplier slices, its live-gate census and the deliberately corrupted carrier coefficient control. The integer checker exhausts2,187 relevant mod3 fixtures and lifts the exceptional carrier root at3.

The [read-only review tool](tools/review_valuation_integer12.py), [normal receipt](data/valuation-integer12-review.json), and [optimized receipt](data/valuation-integer12-review-optimized.json) retain exact commands, source pins, both full scoped receipts and extra local checks. The root all-component verifier was intentionally not run, to avoid duplicating the separately assigned direct-quartic review. Finite diagnostics are not substitutes for the universal argument below.

## What changes in the arithmetic proof

All twelve coordinates and the signed native front are unchanged from the [interpolation review](PROPOSAL_REVIEW_TWELVE_INTERPOLATION.md). In particular,

```
I=s*r*c², S=I*H⁵, Delta=(a+2)²−1,
Df=1+Delta I², Q=Delta² I², delta=Q−1,
V=Df(c−R+4IT)−c, Cy=QV²−1,
Dg=(3P−4)s²+1.
```

The new quintic is the classical intersective carrier

```
Pi(x)=(x²+3)(x³−19),
Phi_H(x)=x⁵+3H²x³−19H³x²−57H⁵.
```

For `u=HT−(X+ac)` and `d²=Dm=1+Delta c²`, its exact reduction is `A+B*d=Phi_H(u+d)`. The main rational-radicand polynomial is

```
delta^16 F32(Sn−A;
    B²Dm, 9S²Df, 81S²Dt, 729S²Dg, S²Cy/delta).
```

The companion replaces its last radicand by `S²delta Cy` and uses the ordinary unscaled norm. Both are literal integer polynomials; the denominator clearing is included in the counted DAG.

### Zero scale and exceptional carrier primes

The quintic has no zero in a real extension of rational degree at most two: its quadratic factor has no real root, and `x³−19` is irreducible by Eisenstein at19. Since the unchanged front gives `H≠0`, `Delta>1`, and `Dm≥1` on every integer assignment, `S=0` specializes either final polynomial to the nonzero expression `(A²−B²Dm)^16`. Thus every zero has `I,s,r,c≠0` and `Q>1`. This precedes all guard and native-decoding assumptions.

Intersectivity is also fully justified. For an odd prime other than3 and19, either the cubic has a simple root, or its irreducible Frobenius is a three-cycle; its discriminant `−27*19²` then gives a simple root of `x²+3`. At19, the quadratic root4 is simple. At2, the cubic root1 is simple. At3 the cubic root is not simple in the original coordinate, so the proof correctly substitutes `x=1+3t`:

```
(1+3t)³−19=9(t+3t²+3t³−2).
```

The parenthesized polynomial has a simple root2mod3 and derivative1mod3. Its lifts supply roots to arbitrary powers of3. Prime-power lifting followed by CRT proves the required root modulo every nonzero integer. No false simple-root assertion is made at3 or19.

### The replacement for monotonicity

The former global positivity bound on `B` is unnecessary. The actual affine front gives, on **every** assignment,

```
q≡X≡−1, a≡H≡Delta≡0,
Dm≡Df≡Dt≡1, delta≡Cy≡−1, u≡B≡1  (mod3).
```

For `Dt`, use `XY²≡−Y²`, so its consecutive product is `Y⁴−Y²≡0 mod3`; this covers `Y≡0` as well. The exact odd remainder is

```
B=5u⁴+10u²Dm+Dm²+3H²(3u²+Dm)−38H³u,
```

which indeed reduces to1mod3. Consequently `B≠0`, `delta≠0`, and `3|H` unconditionally. The carrier is not monotone, but no monotonicity premise is used.

### Noncancellation covers all subsets and signed radicands

After `S≠0`, divide a vanishing conjugate factor by `S`. The five root terms may be ordered as

```
B sqrt(Dm)/S, sqrt(Cy/delta),
3sqrt(Df), 9sqrt(Dt), 27sqrt(Dg).
```

The first four squared3-adic valuations are `−2v3(S),0,2,4`, with `v3(S)≥5`. For nonzero `Dg`, the last is `6+v3(Dg)≥6`; it can be odd. Omit the last term if `Dg=0`. Every subset containing at least two surviving terms therefore has a unique least squared valuation, and that least value is even.

Here is an algebraic proof sufficient even when radicands are negative. Divide such a subset by the rational power of3 at half its least squared valuation. Its squared radicands now lie in the localization `Z_(3)`, exactly one being a unit and all others divisible by3. The formal conjugate norm of their zero-centered sum is an integer polynomial in those radicands. Modulo3 it reduces to a positive integer power of the unit radicand, so cannot be zero. A vanishing signed sum would make one norm factor zero, a contradiction. A nonzero singleton cannot vanish either.

Apply an automorphism of the multiquadratic splitting field to the rational root sum and subtract. Any irrational root moved by that automorphism would give a forbidden nonempty signed subset sum. Hence every term is rational. This uses neither independent square classes nor realness of the guard. In particular an imaginary guard root is excluded by this very argument, rather than assumed absent. An odd guard valuation is harmless because the unique minimum of a multi-root subset always comes from an earlier term.

The rational roots of `Dm,Df,Dt,Dg` are integers. The rational auxiliary root separately becomes integral by the unchanged adjacent-coefficient Pell descent with `Q>1`; for the integral companion, divide its extracted root by `delta` before applying that descent. From `Dg≥0` and `s≠0` one gets `P>0`, then `G>0` and `eta*zeta>0`. The main homogeneous divisibility restores the same integer `gamma`. Thus both variants recover precisely the previously reviewed generalized signed kernel, with no new parity assumption on `I/c²`.

## Completeness and attained degrees

The witness-selection order is unchanged: canonical native data, joint-positivity `t`, guard witness `s`, one strong pair `I,f` with `4sc²|I`, then the intersective class and its auxiliary interpolation, and finally `n`. The inherited theorem fixes `I,f` before asking for any residue of `T mod I`, using period `4mf`, not `4m`. The new carrier's intersectivity supplies `I|Pi(T+gamma)`, hence `S|A+B*d`. Taking

```
n=(A+B*d)/S+y+3f+9tau+27g
```

makes one norm factor vanish; replace `y` by `delta*y` for the integral companion. `n` is unrestricted, and the valid zero guard case `P=1,s=1,g=0` remains available. No later witness changes `I`.

For the principal equation `cn=S²Cy` has degree150. Every other candidate in the homogeneous cleared norm has strictly smaller degree: `delta*Z²` has degree102, and `delta` times the four integer radicands has degrees102,120,134,146. The unique top contribution is therefore `cn^16`, degree2400. With `a0=2^7*3^5*beta^4*j^4*w*v`, `I0=src²`, and `b=4I0T−R0`, it is

```
2^320 *a0^288 *I0^128 *b^32.
```

The coefficient at `j^1152 w^288 v^288 s^160 r^160 c^320 T^32` is exactly `2^2400*3^1440*beta^1152>0`. For the companion, the unique largest radicand `S²delta Cy` has degree182; its sixteenth power has degree2912, with attained coefficient `2^2848*3^1760*beta^1408` at `j^1408 w^352 v^352 s^192 r^192 c^384 T^32`. Thus the stated degrees are exact at the actual fixed coefficients, rather than only generic gate upper bounds.

The fixed-prime replacement is a valid global improvement of the two twelve-variable forms. The already proved pointwise shared-norm and prefix identities are promising subsequent optimizations, but no smaller child count is promoted by this review without a materialized complete DAG and its own exact certificate.

Root independently read the complete `PRIME_TWELVE.md` proof, checked the
localization norm argument for every changed-sign subset (including the
odd-valued or imaginary guard), the exceptional-prime carrier lifting,
zero-scale exclusion, homogeneous congruence and exact leading degrees.
Root also replayed the focused read-only checks in both modes, preserving
both full scoped receipts separately. No gap was found in the new reduction.
