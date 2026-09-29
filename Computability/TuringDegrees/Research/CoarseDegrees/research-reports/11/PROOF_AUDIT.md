# Proof audit

Date: 28 September 2026. Mathematical status: conventional proofs, not an
independent referee report and not Lean/Rocq verification.

## Dependency boundary

The only non-elementary coarse-computability inputs are:

1. HJKS, Theorem 3.7, cone-avoiding compactness, relativized to a background B.
2. HJKS, Theorem 4.2, generic trivial core, relativized in the explicit form
   `intersection_{D approx G} Low(B join D) = Low(B)` for G 1-generic over B.

The relative versions keep B in every oracle computation; all descriptions still
range over arbitrary binary sets. The article isolates these inputs as Theorems
3.3 and 3.5. The robust-radius corollary is the contrapositive of compactness.
Ordinary Turing reducibility, jump strictness/monotonicity, and enumeration of
oracle programs are standard foundational background. Generic coordinate
invariance, no noncomputable bases, absence of background-computable descriptions,
and the relative low generic construction are proved in the article.

No result from the repository's unverified higher-computability package is used.
No conclusion is justified by a claim that a Lean theorem exists without checking
its assumptions. No formal verification is claimed for this article.

## Main logical chain

- Counting controls finite interleaving and finite XOR error propagation.
- Block majority gives per-description, per-generator exact recovery with a
  nonuniform finite correction.
- Positive-density columns and tail density 2^-m verify the preexisting C4 sketch.
- Robust radius and the relative generic-core theorem give the transfer lemma.
- A missing-mask affine replacement makes every proper observation a projection
  of generic coordinates, without supplying the unauthorized secret to the final
  reconstruction map.
- Coalition reconstruction uses only its fully observed codes.
- Replacing those codes by m-column truncations changes at most one output stream
  per fully observed component, with error at most 2^-m in each such stream.
- The transfer lemma puts each core member below a finite join B_(C,m) of
  authorized generators. This proves the nontrivial upper inclusion.
- Decoding the all-of-C component gives the lower inclusion.
- Private generic streams prevent P-computable descriptions. Since the entire
  intended core is below P, the leastness criterion excludes a least degree.
- The full exact join recovers P and all master generic coordinates. This proves
  H equivalent to P join G and the relative jump bound.

## Detailed quantifier checks

### The ideal presentation is not the ideal

P is a single oracle presenting a two-parameter array of generators. Every ideal
member is below some finite join, but P may not belong to the ideal. Exact codes
recover their presentations uniformly. Coarse descriptions recover each generator
with potentially unrelated finite corrections. The proof never exchanges these
quantifiers to conclude recovery of the infinite presentation.

### All masks are jointly generic

One master tuple G is chosen 1-generic relative to P. Its coordinates are then
used as the masks and padding streams. The proof does not assume that independently
choosing several individually generic streams makes their joint tuple generic.

### Coordinate changes and reconstruction use different information

The affine change for a proper observation may use an unauthorized secret Z_S,
which is computable in P. This is legitimate solely to prove that the resulting
coordinates are generic relative to P. After that transformation, the observed
shares are copied free coordinates. The final truncated reconstruction map
F_(C,m) is computable in B_(C,m), not in P. This separation is essential.

### The transfer lemma has no hidden knowledge of the excluded set

Given A in Core(W), robust radius supplies eta. For any sufficiently accurate
truncation, every coarse description D of its generic coordinates produces an
output within eta of W. Hence A is below B_m join D for every such D. Relative
generic triviality puts A below B_m. A is never inserted into the genericity
background and is not assumed below P in advance.

### Error sets are controlled at the correct scale

Extracted periodic and dyadic channels have fixed positive density. Their error
fractions are bounded by a fixed constant times the original error fraction.
Every XOR or reconstruction uses finitely many inputs. The infinitely many
ideal-code columns are handled by a tail of explicit density 2^-m, not an invalid
claim that a countable union of density-zero sets has density zero.

### No uniform finite correction is claimed

Majority decoding computes a finite variant. The proof then hard-codes that
variant's exceptions. A uniform exact decoder for every description is impossible
for noncomputable targets; Proposition 5.3 gives the general reason.

### No least does not mean no minimal

The common spectrum is upward closed and its common lower cone is the core.
It has a least element exactly when some core member computes a description.
This excludes least elements of the constructed spectra, not arbitrary minimal
elements. No classification of the full spectra is claimed.

### The jump bound is relative and simultaneous

Choosing G at or below P' gives (P join G)' equivalent to P'. For the full
construction, H recovers P and G, so H' is P'. For a proper coalition the proven
bound is (P join X_C)' equivalent to P', not necessarily X_C' equivalent to P'.
Private padding supplies the strict lower inequalities; jump strictness supplies
the upper ones.

### Edge cases

- n=1: one ideal code plus one private generic stream; the theorem still holds.
- A singleton component has zero mask coordinates and one parity constraint.
- Empty coalitions are computable and have the computable core.
- The access family may be empty. Then all views are generic; no recovery of P
  from the full exact join is asserted, only the relative P-joined bound.
- If the prescribed ideal is computable, authorized/unauthorized cores may
  coincide; the stronger genericity clause still applies to unauthorized views.
- Arbitrary total-function representatives are handled by binary normalization
  and the graph coding of Turing degrees.

## Attribution and significance

The single-ideal theorem is already the C4 sketch, with closely related coding in
HJS Theorem 3.11(2). The finite additive sharing architecture is classical. The
article's proposed contribution is the simultaneous arbitrary monotone ideal
profile, with a proof of no unintended core information, simultaneous
nonattainment, the common relative jump bound, and the stronger generic
unauthorized-view refinement. Priority is not established.

## Executed checks and visual verification

`checks/verify_finite.py` was executed successfully; `checks/results.json` records
the exact finite ranges and counts. These are not infinite theorem verification.

The PDF was compiled with three passes of pdfLaTeX. The final LaTeX log contained
no unresolved references, undefined citations, overfull boxes, or missing-character
warnings. All 28 pages were rendered for layout inspection; overview sheets and
selected full-size pages were inspected. The final table of contents was placed
on its own page with a reading guide. Text-box boundary checks found no page-edge
violations. These checks certify document production, not the mathematical proof.
