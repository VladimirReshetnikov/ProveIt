# Sources and provenance

Retrieval date: September 20, 2026.

These notes identify the inspected public primary records for the target
and candidate formulas, and the mathematical definitions linked by the
OEIS entry. They are not full copies of third-party pages.

## Selected target

- https://oeis.org/A381190
- https://oeis.org/A381190/internal
- https://oeis.org/A381190/b381190.txt

The internal record was revision 16, timestamp January 7, 2026, 10:23:48.
It attributes the sequence to Eric W. Weisstein (February 16, 2025),
terms from n=14 onward to Christian Sievers (January 2, 2026), and the
conjectured rational generating function to Joerg Arndt (January 7, 2026).
The entry offset is 3. Its 40 terms cover n=3..42.

The label remained conjectural on retrieval. The site-wide footer's
last-modified timestamp is NOT the sequence revision timestamp. The
provided b-file is synthesized from the entry and is not an independent
second mathematical source for the same values. The source values have
been transcribed, with attribution, in data/oeis_a381190_3_42.txt.

## Graph and minimality convention

- Eric W. Weisstein, Trapezohedral Graph, MathWorld:
  https://mathworld.wolfram.com/TrapezohedralGraph.html
- Eric W. Weisstein, Minimal Dominating Set, MathWorld:
  https://mathworld.wolfram.com/MinimalDominatingSet.html

The graph is the skeleton of an n-trapezohedron. Its graph model has a
2n-cycle, two poles adjacent to the alternating rim types, 2n+2 vertices,
and 4n edges. The n=3 graph is the cube. The article specifies all edges
explicitly so that no information in a picture is needed for the proof.

Minimal dominating means inclusion-minimal among all dominating subsets.
The source explicitly distinguishes this from minimality restricted to
connected dominating sets. The private-neighbor criterion is proved
self-contained in the article.

## Other inspected shortlist entries

- https://oeis.org/A225114
  Formula by Mikhail Kurkov, September 3, 2024: continued fraction.
- https://oeis.org/A244475
  Formula by Alois P. Heinz, June 20, 2022: rational generating function.
  Its programs use sets/Union, so the fifth-largest rank is among distinct
  values, not the fifth element of a multiset of row entries.
- https://oeis.org/A289587
  Formula by Thomas Scheuerle, December 23, 2025: algebraic generating
  function. The entry describes avoidance of 321 and mesh pattern
  (12,174), or the equinumerous class with mesh pattern (12,234).

See candidate_formulas.md for the specific target expressions. These
records substantiate the shortlist; no inference about their solution
status beyond the inspected conjectural labels is made.

## Mathematical provenance

The classification, marked-block proof, refinements, and consequences
are developed in the article itself. No pre-existing source is claimed
for this proof, and no claim of global novelty or literature priority
is made. The accompanying OEIS-style note is a draft only; it was not
submitted and the OEIS entry was not edited.
