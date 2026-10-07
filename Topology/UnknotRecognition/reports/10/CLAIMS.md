# Claim ledger

## Proved mathematical statements

1. A compiled genus-zero F2 dotted-cobordism composition factors as
   `Omega(extra_dots * P_left(f) * P_right(g))` through the square-zero component
   algebra. Closed output components are counits; positive genus and two dots
   on one component vanish.
2. Each output coefficient has at most one component-dot source. This gives
   direct reconstruction rather than branching separately from every input term.
3. Ranked subset convolution (the classical Bjorklund–Husfeldt–Kaski–Koivisto
   method) gives a `poly(w) * 2^(w/2)` bit-time dense composition algorithm on
   w boundary endpoints. Exact packed integer lanes have a proof excluding
   cross-lane carries. This is not a new invention of subset convolution.
4. With nonempty left/right input blocks and no extra dots, component projection
   is exactly observational equivalence under all opposite-operand compositions.
   The universal linear-summary dimension is 2^k; any sufficient fixed-length
   deterministic summary requires at least 2^k bits. This is not a lower bound
   for knot recognition or for restricted structured input families.
5. Forced extra dots reduce the mathematical quotient dimension to 2^(k-|E|).
   The current code handles extras but does not exploit the smaller convolution
   dimension. Ordinary matching compositions have no extra dots.
6. Explicit noncrossing zipper triples exist with r=s=q*d and t=k=q on
   2*q*(2*d-1) endpoints. Thus fixed-component compression is realized by actual
   planar matching compositions, not only arbitrary component arrays.
7. Explicit Khovanov object multiplicity can be exponential at two-point boundary
   on long connected-sum tangles. Existing connected-sum reduction can defeat
   this example as a recognition input. This is a representation obstruction,
   not a decision-problem lower bound.
8. A strict lexicographic trace with length L, coordinate cap g and support cap s
   has exactly N=sum_{j<=s} binomial(L,j)*g^j possible states. This upper bound is
   sharp for the abstract restart model. The rank potential is explicit.
9. Polynomial L,g and logarithmic s imply quasi-polynomial restart counts.
   Primitive work, state encoding, uniform reachability bounds, and decision
   correctness are additional hypotheses, not consequences of the count.

## Implemented and executed

- Standard-library numerical component kernel, exact integer convolution,
  validation and cooperative callbacks; per-scanner optional adapter.
- Exact restart counts, lexicographic ranks and inverses, finite-trace audit.
- 15 test methods, zero errors and failures. Structural counts in tests.json.
- Paired kernel microbenchmarks with raw rounds, A/A controls, equality checks,
  separate compilation time, and a severe sparse negative control.
- Compiled, rendered, and inspected article PDF.

## Supplied but not executed against a complete checkout

- integration/check_repository.py, including optional direct closed-PD scans.
- Full fastunknot pipeline/regression suite, Rust port and tests, and race behavior.
- Whole-input performance comparisons and default production integration.

## Not claimed

- An unrestricted quasi-polynomial unknot algorithm.
- A uniform sparsity or low-entropy theorem for actual topological hierarchies.
- That hierarchy certificate existence implies efficient certificate construction.
- That zero-complexity layers are free or geometrically interchangeable.
- That the capped adapter has the unbudgeted dense asymptotic composition bound.
- That the shipped adapter implements the article's sharper dense-transfer
  scanner envelope: transfer is deliberately left unchanged.
- That arbitrary scan frontiers have a common disc-boundary cyclic order.
- Recognition speedups of 86x or 402x: these are specific kernel measurements.
- Robust k=4 improvement: its observed paired ratio range crosses one.
- First-in-literature priority, formal proof-assistant verification, or peer review.

## Required before enabling by default

Run the supplied checker on the actual checkout, run the complete repository
suite, verify the Rust port independently if adopted, and collect paired full
scan/recognition timing with memory, warm-cache reuse, compilation cost, and
compressed-call coverage. Preserve exact fallback and UNKNOWN semantics under
resource budgets. For the hierarchy program, prove all hypotheses of the
conditional theorem uniformly over the construction, not merely on observed
successful traces.
