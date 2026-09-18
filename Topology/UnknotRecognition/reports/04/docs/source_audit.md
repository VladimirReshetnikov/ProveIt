# Source audit and missing implementation obligations

This is an implementation audit, **not** a claim that the announced theorem is
false or that a quasi-polynomial implementation is impossible. It separates
what the supplied slides state, what later outside research supplies, and what
is executable in this archive.

## Supplied notes: Marc Lackenby, February 2021, 109 PDF pages

The page numbers below refer to the uploaded `quasipolynomial-talk.pdf`, not a
shorter handout of the talk.

| Pages | Source content | Implementation status here |
|---|---|---|
| 11–14 | Announces `n^O(log n)` recognition for an n-crossing diagram | Not established for delivered code |
| 18–26 | Boundary patterns, violating discs, essential hierarchies | Terminal pattern-on-ball graph classifier only |
| 43–53 | Basic hierarchy construction and simplification flowchart | Full hierarchy engine not implemented |
| 54–59 | A lexicographically decreasing surface-complexity list | Bounded-digit arithmetic checks implemented; geometric decreases not implemented |
| 60–65 | Iteration count from bounds g and L | Implemented with base g+1 for inclusive digits 0,...,g |
| 66–74 | Quadratic surface complexity, compressed hierarchies, multisurfaces, Heegaard/Cheeger speedups | No claim that these bounds hold for executable states |
| 75–78 | Generalized Seifert construction retaining the embedding in S3 | Not implemented |
| 82–90 | Multisurface rank and compression behavior | Not implemented |
| 91–108 | Logarithmic-depth strategy and Cheeger-region simplification | No constructive Cheeger update or global restart potential implemented |
| 109 | Combined algorithm, including named CUT, BUILD, HAKEN, WEAKLY REDUCE and SIMPLIFY procedures | Those procedures are not replaced by no-op stubs or exponential searches |

Page 8 separately lists Khovanov homology as an unknot-recognition approach.
The executable reference recognizer uses that **different** route. It is not
an implementation of the final flowchart.

The final-page image was inspected as a flowchart, including its restart and
tail-discard arrows; it was not interpreted solely from the linearized text.
The Cheeger test alone is not the Cheeger update. Likewise, constructing a
dual graph is not sufficient to lift a violating cycle back through a
compressed hierarchy.

## Outside research checked

Marc Lackenby, *Incompressible surfaces, hierarchies and unknot recognition*,
arXiv:2607.23350v1, 25 July 2026, gives a detailed related hierarchy algorithm.
Section 9 explicitly separates a count of iterations from running time:
some steps lack the precision needed for a running-time estimate. Its bound
is `L(g+1)^L`. Section 10 obtains a linear hierarchy-length bound in its initial
q-complexity. These statements do not by themselves specify the slide deck's
logarithmic-depth implementation.

Proposition 2.6 supplies the finite dual-graph criterion used in `pattern.py`.
The implementation retains both small exceptions K3 and K4. The 3-ball
hypothesis is required independently; a graph result is not a general
manifold recognition result.

These observations concern the cited versions. They are not a claim to have
proved the absence of every other manuscript or implementation.

## Concrete obligations for a full quasi-polynomial port

**Representations.** Specify the layered handle structure, ambient S3
embedding, boundary-pattern labels, thin/thick surfaces, normal coordinates,
regluing maps, and Morse data. State polynomial bit-size invariants relative
to the original diagram size. A normal surface may have exponentially many
discs despite a short binary coordinate vector.

**Constructing multisurfaces.** Give explicit algorithms choosing independent
relative homology classes and embedded representatives. Prove the required
pattern-sensitive complexity bound and preserve it under subsequent
compression. Enumerating bounded-genus or fundamental surfaces is not a
replacement for a bounded-time construction.

**Compressed cuts and updates.** Implement cut, component, Euler
characteristic, orientation, and pattern operations on compressed data.
Avoid expanding all parallel normal pieces. Track regluing information to
lift certificates. Merely citing Agol–Hass–Thurston compression does not
implement the surrounding hierarchy bookkeeping.

**Violating discs.** Produce a combinatorial curve and an embedded disc in the
appropriate terminal ball, and lift its boundary/intersections to earlier
surfaces. Determine the actual last surface encountered. A separator returned
by `pattern.py` is only an obstruction in the dual graph.

**Compression and weak reduction.** Implement SIMPLIFY MULTI-SURFACE,
HAKEN'S LEMMA and WEAKLY REDUCE, with explicit preservation/progress lemmas.
Compression and boundary compression have different tail-discard effects;
choosing the wrong reset changes both correctness and running time.

**Cheeger-region processing.** Implement recognition of the necessary
Heegaard-Morse hypotheses, construction of the modified splitting, and its
progress measure. Checking the numerical inequality on genera is insufficient.
Prove a bound on restarts as well as the inner hierarchy length.

**End-to-end cost.** Prove that every maintained size, every digit bound,
every hierarchy depth, and every outer restart satisfies its bound, uniformly
over every valid input and every branch of this particular implementation.
Only then multiply the step count by the bit cost of a step. The arithmetic
identity alone proves no topological running-time bound.

## Why some tempting alternatives do not establish the target bound

A polynomial-length unknot certificate does not imply a polynomial or
quasi-polynomial deterministic search for it. A polynomial number of hierarchy
iterations does not help if each iteration expands an exponential surface.
A depth cap that returns UNKNOWN is a bounded search, not a total decision
algorithm. Normal-surface libraries, Reidemeister search, invariant filters,
and the Khovanov recognizer included here may be useful reference backends,
but their running times cannot silently inherit the slides' announcement.

The report proves the delivered reference algorithm's actual exponential
upper bound and its explicit `2^n` state-enumeration lower bound.
