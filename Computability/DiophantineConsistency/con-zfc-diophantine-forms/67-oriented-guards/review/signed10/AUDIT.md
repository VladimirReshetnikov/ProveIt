# Independent review: split116 plus congruence two-root norm

Reviewed artifact: ../../signed/generated/sun10.json, SHA-256 380a168dfdfebe84a80438a1de0a2a3e301e742e38eb61e391bc1c6d745d3439. Snapshot hashes are in SNAPSHOT.json. The supplied independent checker passed in fresh copies in ordinary and optimized Python (REPLAY.json and captured outputs). Original mathematical files were not edited by this review.

## Mathematical compatibility reviewed

1. The original 31-positive parent and its entire four-port tuple are retained. Row replacements r14+r2 and r15+r3 are invertible. Splitting homogeneous degree permits linear/quadratic label collisions without cross-interference: D2 U² + D1 U + D0, with the displayed factorial weights, extracts twice each row. The checker compares the extracted sparse polynomials, not just sample values.
2. The pre-binary estimates use the positive leading D2 coefficient and dominance over potentially negative D1,D0; they do not infer positivity from positive inputs. The shared word ell+g encodes successors only after low-mask decoding. Borrow-tolerant marked cells test zero despite incoming carries −1 or 0. The exact threshold exponent agrees with the actual mask population, so the binomial bridge is not merely a one-way carry implication.
3. The new restrictions b=6t+4, g=bg0, h=bh0, k=b(3k0+2) give b even/nonzero, b=1 mod3, X odd, X=0 mod3, X+1=0 modb, K=0 modb and mod3. Consequently Q=1 modb² and mod3, gcd(b,Q)=1. C+1=0 mod2b implies 4b divides D. Thus a/b is odd whereas d/b is even on every integer assignment. This proves a differs from d before positivity or any Pell recovery.
4. The rational two-root lemma is valid with arbitrary signed candidate radicands: if a differs from d and (q²−a−d)²=4ad, q cannot vanish; the explicitly constructed rational roots of a and d must be integers. This recovers both square conditions and Sigma divisibility without squaring away an unresolved branch.
5. In a=r[1+(3Delta−1)rz²], coprimality, r=1 mod3 and a square force both factors to be positive squares. Repeating this with r=bQ recovers positive square b and Q. Nonzero z then forces Delta>0. This is a genuine unconditional sign exclusion, not an assumed witness-domain restriction.
6. For clean proof order, explicitly derive 0<g<2 Ccal before invoking the reverse bridge: Delta=g K²(8 Ccal³−g³)−32g²(C−KL)² Ccal³>0 and Ccal>0 imply g,K nonzero, g>0, and g³<8 Ccal³. Then all pre-binary X,Y and source-range bounds apply. Also l=0 would make Q=1−K² nonpositive, impossible. The automatic odd f supplies the remaining nonvanishing condition.
7. Completeness uses cofinal b=4^s, so t=(b−4)/6 is integral. Positive coordinate weights give b² dividing g and X+1. The constructive bridge's exact Lucas C and K values imply b divides h and k, with k/b=2 mod3. These are proved from recurrence parity and v2(A−2)=v2(P−2)=1, not assumed tunability of arbitrary bridge witnesses.
8. Pell solvability of u²−(3Delta−1)r z²=1 supplies the chosen z; the nonsquare condition follows modulo3 because 3Delta−1=2 mod3 and r is a positive square. The imported residue interpolation must permit xi divisible by that chosen z and a chosen y residue. Under precisely that stated interface, the quintic local-root merger and integer m complete the forward construction.

## Degree and trust scope

The supplied exact-degree checks use the actual four coefficient payloads and nonzero top-degree residues in three finite fields, alongside the propagated upper degree. They certify degree 3,671,340 and 522 live operations for this circuit. This is an improvement in both measures over the preceding 8,469,528/533 split116 ten-integer form, while the large-degree 513-operation baseline remains cheaper on operation count alone.

The new composition is mathematically coherent under the explicit inherited source/compiler and Sun theorem interfaces. This review does not independently reprove all imported number theory, build Lean/Rocq, or provide an object-language ZFC proof. Numerical tests are not universal proof substitutes. No global minimum is asserted.

## Requested document fixes

Both requested document fixes are resolved in the final snapshot: the imported tail is proper TeX and the Delta-to-source-range ordering is explicit. The emitted circuit is unchanged. Final normal/optimized fresh-copy replay receipts include the added actual signed-congruence and Lucas recurrence diagnostics.
