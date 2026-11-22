# Metric chapter sources and claim boundaries

Accessed with the web retrieval tool on 2026-11-19 (user-facing date).
The proofs and quantitative constants in the chapter were developed here;
these four MathWorld pages establish which source statements are being
replaced and the meaning of their classical terminology.

- https://mathworld.wolfram.com/TychonoffTheorem.html
  - Tool source: `turn793705135view0`.
  - Source statement: compactness of arbitrary topological products, plus a
    reference to Kelley (1950) concerning the axiom of choice.
  - Chapter replacement: explicitly presented countable bounded metric
    products, with primitive-recursive nets/basepoints and supplied uniform
    completion procedures. No arbitrary open-cover compactness is asserted.
  - Source correction: a compact product need not have all factors compact
    if the product is empty. The converse requires a nonempty product.
- https://mathworld.wolfram.com/UrysohnsLemma.html
  - Tool source: `turn793705135view1`.
  - Source statement: continuous separation of disjoint closed sets in a
    normal space, with an explicit convention about normality/T4.
  - Chapter replacement: supplied located 1-Lipschitz distance data, with a
    global or effectively supplied local positive denominator margin. The
    quotient a/(a+b) has Lipschitz constant 1/delta under a global margin.
- https://mathworld.wolfram.com/UrysohnsMetrizationTheorem.html
  - Tool source: `turn793705135view2`.
  - Source statement: equivalence between second-countable regular T1,
    separable metrizable, and embeddable in the Hilbert cube.
  - Chapter replacement: a coordinate-metric construction with explicitly
    supplied inverse neighborhood data, and a concrete Hilbert-cube
    embedding for a metric presentation with dense-sequence locator.
    The regular-space-to-coordinate extraction is not claimed here.
- https://mathworld.wolfram.com/Compact-OpenTopology.html
  - Tool source: `turn793705135view3`.
  - Source statement: subbasis [K,U], comparison with uniform convergence
    on compacta, evaluation and exponential law under classical hypotheses.
  - Chapter replacement: finite-net supremum metric, finite overlapping
    dyadic-box cylinder comparison, and quantitative evaluation/currying
    with supplied moduli. Extracting a uniform image margin from a bare
    pointwise inclusion is not claimed.

## Constructive points checked during drafting

1. Countable product points require a supplied uniform basepoint family;
   arbitrary nonempty-factor choice is not invoked.
2. Infinite weighted sums are evaluated through k+2 coordinates and an
   explicit dyadic tail bound.
3. Locatedness and positive distance certificates are not inferred merely
   from set-theoretic disjointness or negative closed-set descriptions.
4. Countable separating functions alone do not give an effective inverse
   neighborhood transformation; the required certificate is explicit.
5. Compact-open box covers overlap. An exact adjacent closed-box partition
   would invite an unjustified side decision for an arbitrary named real.
6. Approximate extrema are proved; exact maximizing points are not claimed.
7. Every reference to arbitrary procedures is schematic for fixed PR
   definitions. No universal primitive-recursive evaluator is posited.

## Lean verification

Compiled with Lean 4.32.0 (commit
8c9756b28d64dab099da31a4c09229a9e6a2ef35).

- `productSpace`: checked precision-space product interface; Lean axiom
  report lists `propext` and `Quot.sound` (via function extensionality).
- `uniform_comp`: checked, no axioms reported.
- `image_net_cover`: checked, no axioms reported.
- `limit_unique`: checked; `propext` reported.

These are semantic Lean interfaces and lemmas. They do not constitute
object-level iPRA proof-predicate witnesses. The file clearly marks the
finite rational implementations and proof compilation still to be done.

The two supplementary source entries were also opened:

- https://mathworld.wolfram.com/EuclideanTopology.html
  (`turn540287713view0`): Euclidean metric topology, open balls and intervals.
- https://mathworld.wolfram.com/Homeomorphism.html
  (`turn540287713view1`): continuous bijections with continuous inverses;
  the explicit open-cube homeomorphism is proved independently here.
