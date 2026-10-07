# Formalization and integration plan

No Lean source or Lean verification is claimed in this package. This plan is a
proposed dependency order, not evidence that the named interfaces are already
present in Mathlib or ProveIt.

## Stage 1: the exact finite seed

Define `WeightedSeparating weights D modulus` as injectivity of the ordered
weighted-sum map on tuples from a finite alphabet. Do not replace ordered
injectivity by a conventional unordered Sidon predicate.

Prove the `(1,5,10)` seed on `ZMod 80` using reduction modulo 5 and the
four-way partition modulo 16. A finite decidable check can be an independent
certificate, but the short structural proof is preferable for readability.
Also formalize distinct subset sums of `(1,5,10)`, and the resulting
classification of trivial six-binomial solutions as mirror solutions.

## Stage 2: digit lifting and quantitative embeddings

Define a fixed-length digit encoder. Prove injectivity by recovering the
lowest tuple of digits, subtracting its equal integer contribution, and
recursing. It is incorrect to assume there are no carries in individual
weighted sums: the seed's largest weighted sum is 208, exceeding 80.

Separate these conclusions:

1. injection modulo `80^t`;
2. injection over the integers;
3. transport to any modulus greater than `16 * max S`;
4. cardinality and the real-power estimate giving exponent `log 80 / log 4`.

The exact arithmetic inequality `16640 / 79 < 211 < 256` can be handled before
the logarithmic comparison. Keep the finite theorem useful even if real-power
asymptotics are postponed.

## Stage 3: the cyclic perfect-code obstruction

For a hypothetical bijection, form the integer mask polynomial of the
alphabet. At a primitive prime-power root of unity the product of its weighted
substitutions is zero. Use cyclotomic irreducibility and evaluation at one to
bound the number of vanishing prime-power factors by the valuation of the
alphabet size. The covering `1..h*v <= E+V` gives the distinct-valuation
condition. Specialize to `(1,5,10)`.

This theorem does not need the analytic progression-count development and can
live in a separate algebraic module.

## Stage 4: exact circle combinatorics

First prove the even-palindrome rigidity lemma for a circle partitioned into
three equal half-open arcs. Then apply it to the fractional and integer parts
of `3*N*x`, obtaining the nine-copy transfer. Prove the event equivalence
before proving any measure estimate.

The exact measure is `1/(9*(k-1)*N)`, not merely a collision union bound.
The two-arc example `(4,6,8,0)` modulo 10 should be retained as a regression
example against overgeneralization.

## Stage 5: Haar measure, slice volume, and realization

Define the reduced functional by solving the last binomial coordinate with
coefficient -1. This makes the probability normalization explicit.
Prove the integer label inference under `alpha <= 1/(2^(k-2)*m)`, then the
conditional slice integral. Prove the rational constants independently from
the truncated-power formula.

The Fourier realization needs the progression Vandermonde relation and
independence of the `2^s` cube polynomials `(X+omega.H)^s`. The prime `P` used
in the analytic limit is different from the density-dependent prime `p` used
in the finite coloring. The latter must be fixed before the limit is taken.

For rational alpha, formalize the pullback to modulus `q*P` and the o(P)
cardinality correction. This avoids an exact-density quantifier gap.

## Stage 6: external coloring input and endpoints

Either formalize the Shi–Dong carry-control and layered norm coloring or mark
its theorem as an explicit mathematical hypothesis until that work is done.
It must not appear as an axiom hidden inside a supposedly unconditional
formal result. Independently prove the scale-selection theorem with concrete
parameters `d,c,b,C`, then instantiate it at `(4,27,2,9)` and
`(9,5^8,log_4 80,80)` for lengths four and six respectively.

The exact dimension barrier uses homogeneous odd Taylor coefficients and the
Chevalley–Warning degree sum. Its model restriction is total degree at most
`k-1` for each of `t` polynomial coordinates.

## Interface to existing Section 4 definitions

The inspected file was
`Combinatorics/Ramsey/Lean/GowersSzemeredi/Section04.lean`, blob
`987daf1643df5bd45a9e9202a08fb2f7c579a103`. Its conjecture definitions are
non-asserting. Its parameter `k` in `conjecture_4_2` means progression length
`k+2`; the article's `k` means progression length itself.

Before deriving any statement about those exact propositions, prove the
normalization bridge between `UniformSetOfDegree` and the centered normalized
Gowers norm used here, check small-parameter side conditions, and use exact
rational density. Do not change a proof-status ledger based on a PDF proof or
on the Python certificate alone.
