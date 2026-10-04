# Sources and provenance

Research date: 17 September 2026. Claims about source availability mean only what
was found in this investigation, not a proof that no other manuscript exists.

## Supplied primary source

Marc Lackenby, *Unknot recognition in quasi-polynomial time*, February 2021,
109-slide PDF supplied by the user as `quasipolynomial-talk.pdf`.

Relevant **physical PDF page numbers** (including incremental slide builds):

- 11–14: the announced `n^O(log n)` theorem.
- 24–25: essential boundary patterns and violating discs.
- 26–30: essential hierarchies as nontriviality certificates.
- 53: the basic hierarchy construction/simplification loop.
- 54–59: the complexity is not necessarily literal genus.
- 60–65: lexicographic step-count estimate.
- 66–74: four accelerations and the claimed logarithmic depth.
- 75–78: low-genus surface construction, retaining the ambient S^3 embedding.
- 82–90: multisurfaces and their compression behavior.
- 101–108: Cheeger-region condition with factor 1/3 and depth O(log n).
- 109: final flowchart with named, but not implemented, geometric subroutines.

The supplied PDF is not copied into the archive. Its SHA-256 is recorded in
`results/ENVIRONMENT.json`.

## Other primary sources consulted

1. Marc Lackenby, *Incompressible surfaces, hierarchies and unknot recognition*,
   arXiv:2607.23350v1 (2026).
   https://arxiv.org/abs/2607.23350
   https://arxiv.org/html/2607.23350v1
   Sections 6 and 9 are especially relevant. Section 9 explicitly distinguishes a
   step-count estimate from running time and leaves the bounds on its two global
   parameters unestimated there. This is not treated as the complete accelerated
   implementation promised by the earlier talk.

2. Marc Lackenby, *Unknot recognition in quasi-polynomial time*, Oxford slides,
   34-page compressed PDF.
   https://people.maths.ox.ac.uk/lackenby/quasipolynomial-talk-oxford-compressed.pdf
   Physical page 33 uses factor 1/10 and displays `O((log n)^2)` for hierarchy
   length. This is a **different version** from the supplied February slides.
   That observation is not used as evidence against the announced theorem.

3. Mikhail Khovanov, *A categorification of the Jones polynomial*,
   Duke Mathematical Journal 101 (2000), 359–426, arXiv:math/9908171.
   https://arxiv.org/abs/math/9908171
   Original homology construction and invariance theorem.

4. Dror Bar-Natan, *Khovanov's homology for tangles and cobordisms*,
   Geometry & Topology 9 (2005), 1443–1499.
   https://www.math.utoronto.ca/drorbn/papers/Cobordism/Cobordism.pdf
   Standard Frobenius-algebra/cobordism formulation. The Python implementation
   in this archive is original; it does not copy a knot-software implementation.

5. P. B. Kronheimer and T. S. Mrowka, *Khovanov homology is an unknot-detector*,
   Publications Mathématiques de l'IHÉS 113 (2011), 97–208,
   arXiv:1005.4346.
   https://arxiv.org/abs/1005.4346
   The rank-one detection theorem. The report explains the coefficient-field
   argument needed to apply it to the F_2 computation.

6. Andrew Lobb and Raphael Zentner, *On spectral sequences from Khovanov homology*.
   https://www.maths.dur.ac.uk/users/andrew.lobb/SS_khov.pdf
   Section 2.2 gives the reduced-subcomplex convention over Q and Z/2.
   Our implementation shifts/forgets gradings and uses only total dimension.

7. Knot Atlas, K11n42 and K11n34.
   https://katlas.org/wiki/K11n42
   https://katlas.org/wiki/K11n34
   Sources for the two 11-crossing PD fixtures and their trivial Alexander
   polynomials. Mirror-name conventions vary; total homology dimension and
   unknotness are unaffected. Rank 33 in the archived results is a computed
   value, not inferred merely from the names or Alexander polynomials.

8. Regina engine documentation, `Link`.
   https://regina-normal.github.io/engine-docs/classregina_1_1Link.html
   Source for the trefoil PD example `(1,5,2,4),(3,1,4,6),(5,3,6,2)` and an
   additional check of PD conventions. Regina was not installed or executed.

## Implementation versus sources

`patterns.py` implements the terminal small-cycle test using the dual equivalence
between simple cycles and bonds of a plane graph. The reduction to small bonds
and its detailed proof in the report are this package's implementation analysis.
It does not construct the hierarchy or establish that an arbitrary input manifold
is a ball.

`khovanov.py` implements a different, complete exact algorithm. It is provided as
an explicitly exponential fallback and regression oracle, not as an implementation
of Lackenby's accelerated algorithm.

Tests are empirical software checks. The package contains neither a Lean
formalization nor a formal machine-checked proof of the implementation.
