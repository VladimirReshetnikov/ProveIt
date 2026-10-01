# Claim and proof status

## Proposed extensions, with proofs in article.tex

- Theorem 3.1: sharp fixed-critical-complement overlap, including the r log log
  scale and boundary constant; clipped-kernel reduction with scaled error
  O((log n)^3/n).
- Theorem 3.2 and Remark 8.1: all fixed positive Rényi-order constants, the
  Shannon case, the infinity case, and fixed-order error control; the reverse
  relative entropy is infinite.
- Theorem 3.3: order-zero support limit and the alpha sqrt(n) crossover.
- Theorem 3.4: positive residual for r=0, and its square-root-logarithmic decay
  exponent inherited from the flat geometric/Fabius endpoint.
- Theorem 5.1: eventually exact likelihood reduction, including cancellation
  of the finite early-cap normalization factors.
- Corollary 6.3: quantitative total-variation approximation of the omitted
  coordinates and actual slack by their independent limiting product law.
- Propositions 7.1–7.2: exact polynomial-tail decomposition and all-orders
  inverse-logarithmic expansion, with the endpoint defect retained explicitly.
- Proposition 10.2: transfer from a log-squared endpoint estimate to the
  clipped-kernel defect scale, for every fixed r.

The word “proved” refers to the written mathematical arguments, not to
proof-assistant compilation or independent peer review.

## Background and previous work, not priority claims

Exponential tilting; probability representations of Fabius functions;
exponential-family conditioning; gamma convolution and simplex beta formulas;
geometric-series moment recursion; ordinary central limit theory; and the
leading log-squared small-deviation scale.

The preceding ProveIt paper already proves the variance-fraction classification,
qualitative fraction-one separation, an independent exponential slack, a
geometric boundary law, bridge limits, and a leading full-law overlap. This
article does not rebrand those statements as new. Its contributions concern
precise fixed-complement rates, boundary information constants, the moving
information-order transition, and the flatness-sensitive residual.

## Executed checks

228 exact finite symbolic assertions passed. The script also ran 24 geometric
and 24 simplex crossover numerical cases, four kernel-normalization diagnostics,
and a two-grid boundary refinement comparison. These are not a formal proof of
the analytic theorems. The numerical evaluations are not certified intervals.

## Not claimed

No resolution of a named famous conjecture; no exhaustive worldwide priority
search; no independent peer review; no Lean verification or repository build;
no uniform theorem for r tending to infinity, q tending to one, or Rényi order
tending to zero except on the specifically proved crossover scale; no exact
random-bit sampler; no multi-constraint or nonuniform-digit theorem.

The source question's bounded-complement part is answered for the specified
geometric block family. Its slowly diverging-complement part remains a proposed
research direction in this package.
