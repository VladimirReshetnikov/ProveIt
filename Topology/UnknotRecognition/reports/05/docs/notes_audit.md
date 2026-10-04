# Audit against the supplied 109-slide talk

Status: a complete quasipolynomial implementation was **not** obtained. Page
numbers below are PDF page numbers, including repeated animation slides.

| Source location | What the source contributes | Actual implementation status |
|---|---|---|
| 11–14 | Announced `n^O(log n)` theorem | Not a guarantee of this software |
| 15–23 | Hierarchies and inherited boundary patterns | No complete hierarchy data structure or provenance verifier |
| 24–25 | Essentiality and violating disks | Exact polynomial test implemented only on a known ball's spherical boundary |
| 26–30 | Essential-hierarchy criterion | Used as context; no global hierarchy certificate checker |
| 38–53 | Compression, rebuilding, and the basic algorithm | No geometric hierarchy loop; the separate exact recognizer uses Khovanov homology |
| 54–59 | Lexicographic decrease; “genus” may mean another complexity | Numerical bookkeeping implemented; not substituted for actual geometric complexity |
| 60–65 | A digit-based iteration estimate | Exact base `g+1` implementation and proof; see distinction below |
| 66–74 | Four speedups needed for QP | Their combination is not implemented |
| 75–78 | Generalized Seifert construction using the embedding in S3 | Not implemented; arbitrary cocycle surfaces do not substitute for the genus bound |
| 79–81 | Preserve later work under boundary compression | Not implemented geometrically |
| 82–90 | Independent homology classes and multi-surfaces | Integral cocycle representatives and compressed dual surfaces implemented, but not connected-component extraction, multi-surface intersection/cutting, or simplification |
| 91–100 | Logarithmic depth motivation; Heegaard size; long thin regions | No effective depth theorem established for produced states |
| 101–108 | Cheeger-region Morse conditions and genus inequality | Only the numerical inequality is implemented, explicitly not the geometric conditions |
| 109 | Full flowchart | Named geometric operations below remain missing |

## Final-flowchart operations that are not implemented

**CUT ALONG SURFACE.** Need a complete representation of the cut manifold,
induced boundary pattern, ambient embedding, and old-to-new surface provenance.
Binary normal coordinates are not an implementation of compressed cutting.

**BUILD HIERARCHICAL MULTI-SURFACE.** Need the specified geometric objects,
independence and orientability certificates, correct induced cuts, and a uniform
polynomial complexity bound tied to the original diagram. An arbitrary H^1
basis supplies only an algebraic ingredient.

**SIMPLIFY MULTI-SURFACE.** Need to lift a violating disk to the correct earlier
surface, perform compression/pattern compression, preserve permitted later
surfaces, remove or track exceptional components, normalize, and prove progress.

**USE CHEEGER REGION.** Need to verify the restricted Morse function and produce
the changed generalized Heegaard structure. Comparing three integers is not this
operation.

**HAKEN'S LEMMA / WEAKLY REDUCE.** Need explicit weak-reducing disks, checked
attaching data, the modified layered handle structure, and a bounded global
progress measure compatible with complete hierarchy resets.

The diagram-to-exterior and layered-handle initialization are also absent from
the geometric path. The normal-surface CLI instead accepts an already supplied
ordinary simplicial manifold.

## Base convention and source boundaries

The talk's pages 60–65 use informal base-`g` language with digits bounded by `g`.
This archive uses base `g+1`, since allowing the digit `g` invalidates the usual
base-`g` strict-decrease argument: `(1,0)` and `(0,g)` have the same base-`g`
value. The report proves the corrected numerical lemma independently. The
July 2026 paper, Proposition 9.1, likewise uses `L(g+1)^L`.

This is a distinction in conventions and precision, not a claim that the talk's
announced theorem is false. The talk itself warns that “genus” abbreviates a
related pattern-sensitive complexity. The archive does not silently replace
that complexity by the ordinary genus returned by a generic surface routine.

The July 2026 paper is additional research, not part of the uploaded slides. Its
Section 9 explicitly separates iteration counts from costs of individual steps.
The exact Khovanov baseline is another separate construction; it is not the
implementation of the final flowchart.
