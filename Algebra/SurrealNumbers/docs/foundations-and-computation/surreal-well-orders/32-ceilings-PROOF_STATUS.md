# Proof and verification status

## Mathematical status

The PDF supplies written proofs for its stated theorems. The arguments were
checked during preparation for the class/set boundary, admissibility of graphs,
finite-support localization, successor/limit distinctions, and internal versus
external semantics. This is not independent peer review. No historical-first or
"breakthrough established by the literature" claim is made.

The principal additional arguments are the uniform diagonal formulation, the
conditional general condensation bound, and the definability-ceiling/exact-truth
presentation results. The standard ordinal arithmetic and the repository's prior
polynomial-condensation mechanism are not claimed as newly discovered results.

### Critical hypotheses

1. GBC includes Global Choice throughout the internal presentation theorems.
2. All class families used in sums have one admitted uniform relation as a code.
3. General condensation termination assumes an admitted hierarchy along `W+1`;
   ETR supplies existence. The exact strength of existence remains open here.
4. External spectrum theorems assume a strongly inaccessible cardinal κ in the
   metatheory and use M = V_κ, not an arbitrary countable or nonstandard model.
5. Definability uses fixed predicates G and A and allows all set parameters.
6. The truth predicate is added externally as a new predicate; it is not assumed
   definable in the old structure. The old sequence of individual finite-syntax
   bounds is not assumed to be a uniformly admitted family.
7. External comparison of ordinal types is not claimed to produce an internally
   admitted initial-segment isomorphism.

## Source inspection

Repository paths inspected:

- Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/
  23-termination-RESEARCH_STATUS.md (complete status file).
- The README in that same report directory (scope and antecedent attribution).
- SetTheory/ZF/Lean/ZF/Zf.lean (header and initial 150 lines).

Root tree SHA at one read:
8f7d4a5c8cb87e66534d88ec6698f6f46d32a152

Condensation-status blob:
5333d792f02b0d578b7a9907a30d06b5f154e14a

First-order Lean foundation blob:
b33db57cfb71e00c50fa3c57ea355ee4a9a4d523

The repository was active, so these are a read record rather than a claim of one
atomic snapshot. No full-repository proof audit, build, or mutation was performed.
Primary literature and current Mathlib documentation are cited in the article.
The literature inspection was targeted, not an exhaustive priority search.

## Computational status

The included script completed 689,808 exact assertions with no failures, using
seed 20261004. The category counts are in finite_checks.json.

The checks cover finite digit ranks and comparisons, splitting supports,
grouping nested powers, finite initial-support embeddings, hereditary natural
number representations, and tail-mask identities. Tail masks do NOT simulate
actual finite set-interval condensation: every finite interval is already a set.

No Lean or Rocq proof was generated or checked. Finite computations do not prove
proper-class well-foundedness, the existence of ETR histories, inaccessible-model
assumptions, or the truth/definability results.

## PDF and source quality checks

- Source compiled with pdfLaTeX until references and bookmarks stabilized.
- Final PDF: 27 pages.
- Final LaTeX log: no warnings, undefined citations/references, duplicate page
  destinations, overfull boxes, or underfull boxes.
- All final pages rendered with pdftoppm and visually inspected in page montages.
- Cover, contents, main formula/proof pages, and the dependency table additionally
  inspected at higher display resolution during layout review.
- Programmatic text check found no unresolved `??` markers.
- Text bounding boxes stayed inside a conservative page safety frame.
- The archive excludes build intermediates, page images, and font files.
