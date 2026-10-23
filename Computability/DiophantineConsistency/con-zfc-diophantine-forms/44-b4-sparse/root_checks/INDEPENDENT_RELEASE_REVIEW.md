# Independent mathematical and release review

Review date: 23 October 2026. Scope: the fixed-polynomial sparse carry adapter, the thirteen- and fourteen-integer Jones constructions, the nine-natural/positive finalizer, and the sparse source lemma in the ten-integer Sun construction. The inherited logical/compiler calibration and external Sun bridge are reviewed as explicit dependencies, not independently reproved here.

## Verdict and release status

No mathematical counterexample or universal-proof defect was found in the reviewed constructions. In particular, the interval-weighted thirteen-variable guard is valid, including its canonical completeness estimate; the nine-variable finalizer handles zero, negative, and dependent candidate square classes correctly.

The final review checked the frozen scaled-radix revision `B = a b^4`, with natural `b = 2 + epsilon` and signed `b = 2 epsilon^2`. This revision is mathematically valid under the same fixed scale bounds. The builders, active proof text and validation ledgers were rechecked after the component versions were frozen. Final sparse-family metrics are: nine natural/positive, degree 23,321,536,264 and 1,383/1,378 operations; thirteen integers, degree 226,334,238,192 and 1,409 operations; fourteen integers, degree 226,295,141,096 and 1,420 operations; Sun ten integers, degree 69,554,088,184 and 1,407 operations. The final archive replay and integrity seal remain separate checks recorded by the top-level release verifier.

The only definite release-reference issue found was an absent historical coefficient-interface proof at the relative path recorded in the pinned `sun/sources/data/coefficients_binding.json`. It was reported immediately and the referenced proof was subsequently supplied at `sun/coefficients/COEFFICIENT_PROOF.md`. The pinned binding file itself was not altered. Its older 121-by-8801 tuple must remain distinct from the new native 67-by-8807 tuple.

## 1. Fixed-polynomial carry adapter

The B4 property is sufficient: padding with zeros converts all degree-at-most-four monomial codes to four-multisets, so coefficient matching at `L = 4t` extracts exactly `24P(n)`. No power-of-five-specific transfer identity is needed. The fifth source residual is one at the all-one input, so the shifted sum of squares has strictly positive constant coefficient. This gives unconditional positivity of the leading sparse digit polynomial, rather than assuming the witness code has already been decoded.

For the original radix `B = b^5`, the stated scale/base inequalities imply all displayed bounds. The later revision `B = a b^4` also works, but its hypotheses should be stated as `b >= 2` and `a > max(2z(n+1)^4, 2048z, 8)`, not as `b >= a`. For every `1 <= g < 4bB^t`,

    |2(1+g)^4 D(B)| < 1024 z b^4 B^(8t)
                           = (1024z/a) B^(8t+1)
                           < B^(8t+1)/2.

This is exactly the outer-domain bound needed before the carry predicates hold. Also `4b < B`, and each convolution coefficient has magnitude below `z(n+1)^4 b^4 < B/2`. Consequently the shifted base-B digits are genuine digits, the lower mask forces precisely the desired digit positions, and the upper mask tests the extracted coefficient without accidental carries.

At successful ratio assignments, both `b` and `B` are powers of two. The mask `B-b` therefore has precisely the required zero low bits and set high bits. The packing identity is valid even when `S+T >= N`; the high block is allowed to exceed one base-N digit. Its binary digit sum is still `2 log_2(N) - tau_2(S,T)`. Thus the central-binomial criterion is correctly used in both directions.

Completeness remains cofinal in the selected base exponent. With signed `b = 2 epsilon^2`, choose `epsilon = 2^r`, giving the arbitrarily large odd exponent `1+2r`. This preserves the source's canonical square `omega = 2^(2R+1-k)`. It is not the invalid proposal of requiring an old additive slack to be a square.

## 2. Thirteen-variable interval guard

For positive `cap`, the strict condition

    Delta = g(cap-g)K^2 - cap^2(C-KY)^2 > 0

implies `K != 0` and `0 < g < cap` without assuming any signs for `g` or `K`. The identity

    cap^2[K^2 - 4(C-KY)^2]
      = 4Delta + (cap-2g)^2 K^2

gives the strict original approximation inequality. The recovered interval lies inside the carry adapter's outer domain, so it establishes all required positivity and size hypotheses before the Jones ratio theorem is invoked.

The proof-side choice `Gaux = 8gK^2 + 1` is legitimate: once `d = K^2 - 4(C-KY)^2` is a positive integer, its literal source margin is

    Gaux*d - 8gK^2 = d + 8gK^2(d-1) >= 1.

No source ratio register other than the free margin ceiling depends on this substitution. It adds no equation unknown.

For completeness, the copied `Ratio.lean` construction really chooses `U = (N^2/b)2^(2R+1)`, `Y = floor(rho)`, and the stated Pell-sequence `C,K`. The low half of the binomial expansion gives the stricter remainder bound `0 <= rho-Y < b/(2N^2)`. The literal `ratio_core` estimate then gives `|C/K-rho| < 4/U`, hence `|C/K-Y| < b/N^2`. Because the coded witness satisfies `1 <= g < cap`, and `cap,b <= N`, this implies `Delta > 0` for that very same canonical witness. No square restriction on `s` or `Y` has been smuggled into the argument.

## 3. Signed zero and sign cases

The linear-prefix Pell stack is sound: each new factor is coprime to the whole preceding prefix, and is 1 modulo 4. If the total product is a square, each factor has square absolute value; a negative square cannot be 1 modulo 4. This establishes every prefix's positivity before using it to infer the discriminant signs. Discriminants congruent to 2 modulo 3 are nonzero and nonsquare on the positive branch.

The merger denominator is nonzero on every integer assignment. `J = 4A-5` never vanishes. If `F = 0`, then integrality forces `A = 0` and `E = +/-1`, impossible because `J=-5` divides `E`. The intersective numerator never vanishes because its associated quintic has no rational root. Thus a zero nonvanishing product cannot create an extraneous solution.

The three-root norm proof uses absolute weights and complex roots correctly. A changed nonzero radical has modulus at least one; the largest changed weighted term strictly dominates the preceding terms. This remains valid for negative radicands and repeated square classes. Zero roots are ignored as ineffective sign changes. Rationality of a vanishing signed sum consequently forces every individual root to be rational, hence integral.

The subsequent recovery of positive `h` uses a genuine strict square gap. Replacing `i` by its absolute value preserves all relevant predicates. The `j` adjustment uses the divisibility-implied congruence `F | H-C`, pairwise coprimality of `D,F,I`, and a Pell unit power congruent to one modulo `CF`. For negative `H`, the initial real unit remains positive because `sqrt(1+(G^2-1)H^2) > |H|sqrt(G^2-1)`. Therefore the orbit argument does not omit the negative-index branch.

## 4. Nine-variable finalizer

The strong positivity of the actual input polynomial makes `R`, all required ratio registers, and the divisor `u` positive on every natural assignment. This is essential: the finalizer cannot assume the margin/carry conditions before extracting them.

The identity

    S0^2 - 64DF = t0^2(8D+1) - 64D

is exact. Since `t0^2 >= 9` and `D >= 1`, its right side is strictly positive. Along with `I <= G^2H^2`, it establishes the strict bound `sqrt(a1) < S0GH`. Likewise `K>1` gives `sqrt(a0) < PK`. The removal of old `+1` slack terms is therefore valid.

For a vanishing norm, let the resulting rational root sum be `s = r0 + V0 r1`. If `s != 0`, the identity `2s r0 = s^2 + a0 - V0^2 a1` proves both roots rational. If `s = 0`, the strict bound `|r0| < V0` implies `|r1| < 1`, so both integer radicands are zero. Thus the proof does not assume square-class independence and includes negative candidate radicands.

After rational roots have been proved integral, strict bounds give `|r_i| <= V_i-1`. Therefore the bracket `Z` is at least `M+1`, not merely nonnegative. This makes the sign extraction of `mu` valid even at `n=0`, and the same factor equation forces `u | v`. Conversely the formula produces an integer `n >= 1`. The positive translation is a domain bijection, not an unrestricted-integer reduction.

The degree proof retains the exact cancellation identity for `V1^2-a1`; subtracting naive degree bounds is invalid. The scaled-radix degree was independently recomputed: `deltaV` has degree `9072t+2072`, the inner norm expression has degree `19088t+4372`, and the output has degree `38176t+8744` with diagonal leader `2^1046 a^(9544t+2120)`. The signed leading degrees were independently recomputed as `370496t+84272` and `370432t+84456`, respectively.

## 5. Sun source lemma and imported bridge

The sparse source lemma's lower/upper code bounds apply before the code has its intended digit form. The positive constant coefficient justifies `D_c > 0`; the fixed scale supplies the needed coefficient and packing bounds. The binary digit-sum argument and shifted coefficient test are valid. The explicit finite B4 certificate, rather than the field construction's provenance, is sufficient for the claimed fixed weights.

The Sun finalizer's use of `|a0| > 1` is valid for every candidate with `z != 0`: `b=1+3f` cannot vanish, and `b=1` forces `f=O=0`, giving `a0=1-4z^2`. Its factor coprimality and modulo-three argument correctly recover a positive square `b` and `O>0`.

The remaining positive/reverse bridge and full residue interpolation are explicitly imported. This review does not upgrade them, the K215 calibration, or the fixed-port compiler endpoint into newly compiled formal theorems. The release should retain that distinction.

## 6. Independent executable evidence

The companion `independent_release_checks.py` writes only its own ledger, `INDEPENDENT_RELEASE_CHECKS.json`. It does not regenerate other component artifacts. Its independently implemented checks establish:

- All 402 weighted coefficient recipes equal those obtained by shifting and squaring the literal 22 source residuals.
- The parent hash, four compressed/uncompressed payload hashes, byte sizes, port bit lengths, and all 402 fixed coefficient bounds agree.
- The same old 121-by-8801 tuple is used throughout the sparse nine, thirteen, fourteen, and Sun constructions. The MF port is already the shifted source port.
- All 52,360 B4 sums are distinct both as integers and modulo 1,048,575.
- The saved circuits have acyclic fully live binary-operation graphs and exactly their declared variables and operation counts.
- 4,913 signed assignments have nonzero merger denominator, 94,080 bounded signed-radicand finalizer cases produce no false implication, and 70 exact scaled-radix toy-code assignments obey both carry tests and central-binomial digit-sum packing.
- All listed files in the Sun and nine source-pin manifests have their declared hashes.

The bounded tests are regression checks, not the universal proof. Circuit degrees in the JSON ledger are labeled as claimed degrees; this independent script does not silently present metadata as an independent degree theorem. The mathematical argument and the dedicated exact leading-head certificates supply that separate claim.

## 7. Final freeze checklist

Before sealing the archive, rebuild and verify the scaled-radix branches, then check that the proof formulas, generated graphs, validation timestamps/hashes, exact degree formulas, operation counts, summary tables, and PDFs refer to that same frozen version. Preserve the older construction only if explicitly labeled historical. Keep the fixed sparse-family tuple distinct from the new native compiler tuple. Do not describe modular tests as universal identities or the ordinary proof as a new end-to-end Lean/Rocq certificate.
