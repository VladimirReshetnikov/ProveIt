# Research and verification audit

## Proposed original content

The exact cofinite-span algebra classification, the primitive recovery of the
finite exceptional coefficient extension, the sign-difference polarization
proof, and the explicit ordinary/mixed differential-independence constructions
are offered as proposed contributions. The paper does not assert that all
individual ingredients or all cardinality consequences were previously unknown.
A targeted search did not identify these formulations; no exhaustive
MathSciNet/Zentralblatt or full citation-network audit was performed.

## Imported mathematical foundations

The following are standard inputs, not new claims:

1. Hahn fields and their support/Neumann lemmas.
2. Conway normal-form embeddings of set-sized Hahn workspaces into No or No[i].
3. Finite separable Galois theory and extension of embeddings to algebraic closures.
4. Existence of the normalized Berarducci–Mantova derivation, strong additivity,
   real constant field, and D_BM(omega) = 1.

The finite coefficient-base-change and multiquadratic facts are proved in the
article. The coefficient-field criterion is presented as a preliminary Galois
argument, not a priority claim. The only general-derivation facts used in the
actual-surreal construction are the four standard properties in item 4.

## Distinctions essential to correctness

- The coefficient sign changes act on a multiquadratic intermediate field and
  its Hahn field. They are not asserted to be order preserving or to extend
  to all real-algebraic numbers or all surreal numbers.
- Cofinite span means intersection over finite deletions, not arbitrary
  ordinal initial-segment truncations.
- Characteristic zero, finite-dimensional coefficient vectors, independent
  square classes, and distinct well-ordered exponent indices are explicit.
- The analytic base C(z)((t^Q)) is not a common-domain holomorphic function ring.
  The field L((t^Q)) and O(D)((t^Q)) are both embedded in the meromorphic-germ
  Hahn field M_0((t^Q)); neither is asserted to contain the other. The specific
  constructed functions lie in their intersection.
- Analytic function independence is not asserted to survive point evaluation.
  At z=0, the full-series Taylor jets are rational functions of t.
- The formal Taylor series in z is not an admissible Hahn sum over Taylor
  order at an ordinary nonzero complex z. Halo substitution has its own
  joint-support proof.
- The two derivations on analytic coefficient functions are not automatically
  Berarducci–Mantova differentiation after arbitrary surreal substitutions.
- Continuum cardinality of an independent family does not assert that this
  family is a transcendence basis or a differential transcendence basis.
- Valuation closure is always relative to a specified set-sized value group;
  it is not the fine topology of the whole proper class No[i].

## Proof checkpoints

The core argument can be reviewed in this order:

1. Lemma 2.4: independent coefficient sign automorphisms.
2. Lemmas 4.2–4.4: stabilization, multilinear detection, mixed differences.
3. Proposition 4.5: highest-degree polarization obstruction.
4. Theorem 5.1: primitive exceptional-field recovery and polynomial algebra.
5. Theorem 5.2: finite Galois base change and the affine relation components.
6. Theorems 7.1 and 7.3: Vandermonde tails, binary-prefix sets, triangular
   conversion between Euler jets and normalized surreal derivatives.
7. Lemmas 9.1–9.2: exponential-graph and pole-order spanning arguments.
8. Theorems 9.3 and 10.1: finite mixed-jet rectangles and private index blocks.

All proof claims are mathematical arguments in the article, not results
inferred from a finite experiment. There is no included Lean formalization.

## Exact-check inventory

- BM_restriction: 42
- Taylor_identity: 9
- analytic_derivatives: 27
- binary_prefixes: 136
- dilation_identity: 4
- mixed_difference: 46
- mixed_jet_rank: 48
- multiquadratic: 11
- square_class_examples: 63
- vandermonde: 18

Total: 404; all passed. Python 3.13.5, SymPy
1.14.0; deterministic pseudo-random seed 20260922.
Some checks verify different aspects of one small example. The count is a
check count, not a count of independently proved theorems.

## Bibliographic audit

Repository read: pinned project README and documentation catalogue, opening
spectral-theory source, Laurent-birthday inventory, and a targeted repository
search. This is not an exhaustive review of archived manuscripts.

Primary literature checked for the ingredients and comparisons: Stacks Galois
and Kummer sections; Berarducci–Mantova's abstract and relevant theorem text;
Kaplan–Krapp–Serra's Hahn/normal-form preliminaries; publication metadata and
abstracts for van der Hoeven and Mijajlovic–Malesevic. No claim is made that all
of these papers were read in full. No third-party source paper is redistributed.

## Artifact checks

The delivered PDF was compiled from the included source with three pdfLaTeX
passes. The final log has no undefined references, undefined citations,
overfull/underfull boxes, or LaTeX warnings. Every PDF page was rendered with
Poppler; a full-page montage and selected detailed pages were visually
inspected. Programmatic page-boundary measurements are in layout_audit.json.
No font files, build logs, third-party PDFs, or temporary renders are packaged.

## Changes made when this package was fitted into the collection

These edits are recorded here rather than folded silently into the text above.
Nothing in the sections above is retracted; every scope restriction they state
still applies.

1. Every `\label` in `article.tex` was given the `tail:` prefix and every
   reference updated. No label was deleted, and no label name outside this
   package was changed. Three of the old names were substrings of labels
   belonging to other reports (`polynomial:eq:eulerderivative`,
   `thm:coefficient-limit`, `dyn:prop:halo`); the prefix removes that risk.

2. The restriction of the Berarducci--Mantova derivation to a rational-exponent
   Hahn workspace is no longer reproved here. It is cited from
   `docs/surcomplex/differential-equations/`, whose `diff:eq:HahnQ` fixes the
   workspace and whose `diff:prop:hahnderiv` (equation `diff:eq:hahnderiv`)
   proves the formula. The only step still carried out here is the further
   restriction from real to real-algebraic coefficients. The item-4 imports
   listed above are therefore now imported by citation to a companion report as
   well as to Berarducci--Mantova; they remain imports, not new claims.

3. A cross-reference was installed in both directions with
   `docs/surcomplex/dynamics-and-normal-forms/`. That report's warning
   `dyn:warn:diffalg` declines to upgrade its own transcendence result to
   differential transcendence, because its `H_eps` satisfies a first-order
   linear equation over its base. That warning is true of `H_eps` and has not
   been weakened: the paragraph added there says so explicitly before pointing
   here, and `tail:rem:dynupgrade` here says the same from this side. The two
   reports are about different functions. This report's analytic theorems say
   nothing about `H_eps`.

4. The closing sentence of the proof of `tail:thm:surreal` was rewritten. It
   had attributed both the lower and the upper cardinal bound to the
   independent family. The upper bound is an independent count
   (`|H_0| <= aleph_0^aleph_0`, from countability of the coefficient field and
   the value group) and is now attributed to it. No statement changed.

5. `tail:rem:indexfamily` was added, recording that the continuum-sized theorem
   is about the binary-prefix almost disjoint family and not about all subsets
   of the positive integers: the family indexed by all subsets satisfies
   `xi_{A u B} + xi_{A n B} = xi_A + xi_B` and is not independent.

6. `code/build.py` was corrected to resolve `article.tex` in the package root,
   since the script now lives in `code/`.

The headline claim of `tail:thm:surreal` was re-derived during this pass and
holds as stated. `data/layout_audit.json` describes the originally delivered
23-page PDF and not the 25-page rebuild in this directory; the rebuild was
compiled with three pdfLaTeX passes and its final log likewise has no undefined
references, undefined citations, overfull or underfull boxes, or LaTeX
warnings. The page-by-page visual inspection recorded above was performed on
the original delivery and has not been repeated.
