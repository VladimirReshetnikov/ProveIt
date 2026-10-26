# Review: polynomial equality transports signed zero semantics

Analysis snapshot: `89226e3921bce3e8949fadd12d3efb6914c7630c`. Closing novelty refresh: `7df43cdfacb490cd3ca3acd23e39027efebf8801`.

## Verdict

The proposed universal transport theorem was not found as a substantive proposal in the 23 placed packets a-w or the five currently incoming ZIPs (28 packets total after the closing refresh). It is a distinct, mathematically sound mechanism provided the target carrier is a commutative semiring with additive cancellation. It is not yet a claim of a compiled theorem or an integrated source reduction.

## Exact statement

Let `e f : Expr sigma`, and let `v : sigma -> R`, where R is an additively cancellative commutative semiring. If `e.toPolynomial = f.toPolynomial` as integer multivariate polynomials, then

`e.SemiringZero v <-> f.SemiringZero v`.

The conclusion concerns the existing positive/negative split semantics. It does not equip R with subtraction and does not interpret R as external natural numbers.

## Proof

Write `(Pe, Ne)` and `(Pf, Nf)` for the natural-coefficient polynomial interpretations of the respective positive and negative syntax splits. Their integer images have differences equal to the original integer polynomials. Consequently

`map(Pe) - map(Ne) = map(Pf) - map(Nf)`.

In the integer polynomial ring this is equivalent to

`map(Pe + Nf) = map(Pf + Ne)`.

The natural-to-integer coefficient homomorphism is injective, hence so is its induced multivariate-polynomial map. Reflect the equality to natural polynomials:

`Pe + Nf = Pf + Ne`.

Evaluate at v through the canonical natural-coefficient homomorphism into R. If `Pe(v) = Ne(v)`, substitute and use additive commutativity/cancellation to deduce `Pf(v) = Nf(v)`. The converse is symmetric.

No order, characteristic-zero assumption, no-zero-divisors assumption, or multiplicative cancellation is needed. The statement therefore applies to the existing internal-natural carrier under its actual algebraic instances, including when the ambient set-theory model is nonstandard.

## Necessary boundaries

Additive cancellation cannot simply be omitted. In the Boolean semiring, addition is OR and multiplication is AND. Let e be the constant syntax 1 and f the syntax `(constant 2) - (constant 1)`. Both integer polynomials are 1. But SemiringZero(e) is `1=0`, false, whereas SemiringZero(f) is `2=1`, true because `1+1=1` in that semiring.

Commutativity of multiplication is also needed for using ordinary commutative multivariate-polynomial equality. For example, `xy-yx` is the zero commutative polynomial but need not have equal split evaluations over a noncommutative matrix semiring. Existing SemiringZero may be defined under Semiring alone; the new theorem must explicitly add the stronger CommSemiring hypothesis.

Polynomial equality is not the same as equality at selected numeric test points. A finite evaluation test cannot supply the hypothesis. Use a proved symbolic identity such as `ring`, the existing literal syntax-to-polynomial theorems, or a checked formal certificate.

Keep the executable expression e unchanged: a proof-side comparison with a convenient expression f should not silently alter expression data, witness counts, or compiled programs. If f is adopted as actual executable data, that is a separate cost-preservation problem.

## Nearest prior proposals

- Packet b, `proposals/SemiringSpecialization.lean` and its report's semiring compiler section: standard-natural integer zero is equivalent to split evaluation, so the existing generic semiring gate proof can specialize to Nat. It does not transport arbitrary integer polynomial identities to every cancellative semiring.
- Packets c and h, object-model notes: reuse existing internal semiring evaluator and finite-row machinery; preserve arbitrary internal naturals and avoid import cycles. They do not provide polynomial-congruence transport for signed syntax.
- Packet w, RefinedPair: eliminate complex square-root choices by injectivity of exponent dilation in a formal polynomial identity. This is a different identity-establishment method, not transfer of signed zero semantics into a semiring without subtraction.
- Packet k, `novelty-audit.md`: exploratory natural-difference/order-embedding bounds are search directions, not an explicit ring-completion or universal polynomial transport interface.

## Concrete value and accounting

The strongest potential value is to move repeated expansion of `Expr.splitNatural` out of per-row algebra proofs. Candidate rows occur in ObjectConditional, ObjectZeroTest, ObjectPairingSyntax, ObjectDivModSyntax and related actual quadratic systems. The helper needs a split-polynomial compatibility theorem plus coefficient-map injectivity. Its full proof and imports count against any source-size saving. ObjectTreeCodeSyntax already delegates many algebra obligations and should not be advertised as a large direct saving without a measured residual client.
