# Prime-three separation: ordinary proof and complete replay review

The prime-separation reductions are sound ordinary arithmetic under their stated inherited source34/native/Pell calibration. The useful new endpoint is **16 unrestricted integers, degree108,132 live binary operations**. It trades four degree units for thirteen operations against parity16/112/119. Both full release replays pass, normally and under `-O`. No Lean or internal object-ZFC certificate is added; formalization remains paused.

The archive is `ConZFC_Prime_Separation_13_Integer_2026-10-23.zip`, SHA256 `56fe2af05f811ca3eb75d36f3fbcb2ab46265a7f85425534fff1e70746fb6680`. Its176 original files and175 manifest entries remain intact. [The read-only focused tool](tools/review_prime_separation.py) generates [normal](data/prime-separation-review.json) and [optimized](data/prime-separation-review-optimized.json) receipts, including both full release results and the exact local sixteen-variable norm identity.

| Unrestricted integer variables | Exact degree | Operations | Current comparison |
|---:|---:|---:|---|
|13|1392|205|Dominated by root-fusion13/1392/186 and13/1088/195 |
|14|696|151|Dominated by root-fusion14/696/150 |
|15|244|137|Dominated by parity15/204/128 |
|16|108|132|Lower degree, greater cost than parity16/112/119 |

All are complete literal equations. Fixed numeral leaves and reuse are free; each live binary addition, subtraction or multiplication is charged. The coherent six coefficients are exactly the whole source34 tuple with beta=`2^1064921-1`, MF already shifted, and determinant scales `2^1113,2^666104`. All actual raw hashes match the saturated, root-fusion, fixed-prime and parity reviews, totaling615,883 bytes. No smaller compact tuple is substituted.

## Why the valuation proof works with its fifth guard

The four old normalized roots have squared3-adic orders

```
4, 2, 0, -2v3(H), with v3(H)>=1.
```

For every nonempty subset with at least two old roots there is a unique even minimum. Divide by the corresponding square power of3. The product over all other sign choices has integer coefficients in the squared roots, and modulo3 is a nonzero power of the unique unit square. Thus no signed subset sum vanishes. The same reasoning works when some rational radicands are negative: it is an algebraic argument, without a positivity premise.

If a signed root sum is rational, apply every automorphism of the finite multiquadratic field and subtract its image. A changed nonzero root would give a forbidden signed subset sum. Hence every root is fixed by all automorphisms and is rational. Rational square roots of integers are integral; the auxiliary rational root is integral by adjacent-coefficient descent after Q>1 is available.

The fifth root is weighted27. Its squared order is **at least6**, possibly odd, or the root is zero. The proof does not assert that the guard radicand is a3-adic unit or has even order. Any subset containing an old root still has a unique even minimum; a nonzero singleton consisting only of the guard root cannot sum to zero, and a zero guard root is already rational. This distinction makes the guard fold valid even when its radicand is divisible by3 or negative.

For thirteen variables c is syntactically odd. The fixed affine restrictions make q and Y nonzero, Delta>1 and odd, and `Q=Delta²(2r+1)²c⁴>1` before the guard is recovered. The denominator `Q-1=-1 mod3` is nonzero. Thus folding the guard introduces no circular nondegeneracy premise. For fourteen variables the guard is retained separately and supplies c nonzero before Q>1 is needed.

The main carrier initially yields only `2gamma` integral. Its root d0 is integral, so `Hgamma=d0-D0` is also integral. Odd H then makes gamma integral. Omitting this midpoint argument would leave a quotient gap; it is explicitly supplied.

Soundness restores the ordinary odd strong coordinate and both CRT quotients by integer polynomial formulas. Completeness constructs an odd normalized strong witness at index Rc, then a squared-modulus auxiliary witness, keeping the same calibrated native/determinant family. Canonical c is odd, so the syntactic thirteen-variable restriction preserves existence. The construction does not assert a polynomial inverse for every old zero.

## The sixteen-variable lower-degree tradeoff

This companion retains f and the old strong and guard residuals. Put

```
u=XY²k, t=2u+k, ell=k²-4,
A=u(u+k)+1, Q=I², delta=Q-1,
B=(QV²-1)/delta.
```

At a zero the guard alone gives |c|>1, so Q>1. The strong row and `3|Delta` give `3|I`, hence `Q=0 mod9`. Both A and B are1 modulo3. The two weighted roots `3sqrt(A)` and `sqrt(B)` therefore have distinct even squared valuations2 and0.

The exact literal norm is

```
j=delta*x²+delta(6t+4V)x+9delta*ell-4(V²-1),
h0=12delta*t*V,
N16=j²+2h0*j+576delta*A(1-V²)+144delta²*ell*V².
```

It satisfies the free integer polynomial identity

```
N16 = [delta((x+3t+2V)²-36A)-4(QV²-1)]²
          -576delta*A(QV²-1),  Q=delta+1.
```

Equivalently it is `delta² F2(x+3t+2V;36A,4B)`. The focused tool independently expands all53 terms and verifies the identity, using `t²-ell=4A`. The valuation lemma supplies rational first and auxiliary roots; the first becomes integral by its integer square, and the auxiliary root by the exact Pell descent. Their centered inverses restore both discarded private coordinates. Conversely any old zero supplies `x=6tau+2y-3t-2V`, an unrestricted integer. No parity division or zero-carrier assumption is introduced.

The norm degree is54, while the other three retained rows have smaller degree. Squaring gives attained degree108. The full release reproduces the exact authentic-coefficient degree certificate and all132 live operations. The adjacent parity family takes a different projection, eliminating the odd strong multiplier as one of its roots; its119-operation/degree112 form is therefore a genuine tradeoff, not the same free polynomial counted differently.

## Replays and scope

Both complete modes pass all six literal coefficient reconstructions, byte-identical rebuilding of eight dense/compact circuits, topology and liveness, universal norm and quadratic-algebra identities, independent primary-formula binding and all four exact degree certificates. They also pass the ancillary ten-integer local-identity checks. Those ancillary evaluators preserve their inherited polynomials; this review does not make a new semantic claim for the ten-integer source. No frozen H10 emitter or numeral array is executed.

No defect was found in the new ordinary reductions. The primary13/14 normalization and the16-variable guard/strong prerequisites appear in the required dependency order. Complete finite circuit verification does not establish the inherited universal native/refutation theorem, consistency, or correctness over arbitrary nonstandard internal omega. Those boundaries remain explicit.
