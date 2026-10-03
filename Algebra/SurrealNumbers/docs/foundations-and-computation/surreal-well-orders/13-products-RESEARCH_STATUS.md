# Research and verification status

Date: 3 October 2026.

## Mathematical status

This is an AI-assisted, unrefereed proof manuscript. The main extensions
are presented as mathematical theorems with proofs under their stated
axioms and interpretations. Independent peer review and historical
priority are not claimed. Explicit proofs and precise remaining questions
are supplied.

The fixed-alphabet spectra, singular birthday-cutoff dichotomy, dense
bounded-support core, one-head raw decomposition, and diagonal coding
limitation are credited to existing repository reports. Necessary core
arguments are written out again. The main new cut and automorphism proofs
do not depend on the singular-cardinal dichotomy.

## Critical scope conditions

1. Cut reconstruction uses normalized cuts: the lower side has no greatest
   element. This prevents two cuts adjacent to one code from being
   confused. The all-level condition ranges over set ordinals. Exhaustion
   is a separate condition on coverage of every surreal label.
2. The classification is relative to a supplied coded core and prefix
   system. The pure order does not canonically recover that system.
3. The product nonembedding is proved for arbitrary external maps in a
   full inaccessible-universe interpretation, and for fixed-formula
   uniform maps in KM plus global choice. It is not advertised as an
   unqualified third-sort theorem of bare GBC. The existential-class
   inverse evaluator is explicitly identified.
4. Externally countable models admit arbitrary external embeddings of the
   split order and an external isomorphism of the lexicographic square.
   Such maps need not be internally available uniform definitions.
5. Central termination reserves zero as a marker and excludes it from the
   ordinary alphabet. Admitting zero as a letter would identify distinct
   zero-padded words. Transport to another alphabet is stated explicitly.
6. Ordinary classes of set codes, class relations as parameters, and a
   higher collection of all class relations are never identified.

## Repository audit

Pinned commit: 0ecd158fd163bc4aca0ee40ccf6479ca6cf5f2a8.
Reported commit timestamp: 2026-10-03T17:15:49Z.

Targeted materials:
- The merged surreal-well-orders report and its guide: introductory
  claims, selected core/cylinder and omitted-range proofs, full-model
  and KM nonembedding arguments, formalization discussion, research index.
- The real well-ordering report's guide, for antecedent results and notation.
- SignSequence.lean, source-level carrier, order, birthday, and smallness APIs.
- SignSequenceCut.lean, the actual small-cut construction.

Git blob identifiers:
- Merged article.tex: f20837b76f8d981cb1dce3da79f633e280edad41.
- SignSequence.lean: e2c093860f29b0b9ea312d50099fc4aa89a76a99.
- SignSequenceCut.lean: c5c35afd98a5ad293687367ee9fb0244f94cc91c.

This was not a complete audit of the 115-page merged predecessor report.
No remote files were changed, no Lean project was built, and no new Lean
proof is included. Proposed module interfaces in the article are plans,
not a claim that the files already exist.

## Literature

The bibliography uses the pinned repository and primary sources by
Ehrlich, Kanovei–Shelah, Hamkins–Woodin, and Antos–Friedman. It is a
targeted literature review, not a complete priority search. Current
status of every historical question in those papers is not asserted.

## Executed checks

The delivered standard-library program completed successfully in Python
3.13.5. Its JSON output records all counts. The checks compare independent
finite representations, including rational evaluation of finite surreal
sign strings. They do not verify ordinal-limit arguments, class
comprehension, global choice, or transfinite recursion.

The article was built with three pdflatex passes. All 33 PDF pages were
rendered and inspected in contact sheets; the cut-reconstruction page and
Lean-interface table were additionally inspected as full-page renders.
The final build log contains no warnings, undefined references, overfull
boxes, or underfull boxes. No clipping or overlap was found in the visual
inspection. These are document-quality checks, not mathematical proof
certificates.
