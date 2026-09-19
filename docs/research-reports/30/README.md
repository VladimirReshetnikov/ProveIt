# Prikry symmetry at the measurable threshold

A continuation of the research in `Cardinals4.zip`, prepared for Vladimir
Reshetnikov on 18 September 2026.

## Contents

- `Prikry_Symmetry.pdf`: 21-page research report with detailed English proofs.
- `Prikry_Symmetry.tex`: complete, editable LaTeX source; no external bibliography required.
- `checks/finite_checks.py`: reproducible standard-library Python checks.
- `checks/results.json`: the successful recorded run.
- `manifest.json`: provenance hashes and build/check status.

## Principal result

In an ordinary normal-measure Prikry extension W[c], put lambda = kappa and
q = [c], where the brackets denote equivalence modulo finite symmetric
difference. The exact finite-label classification and the obstruction to a
nonempty finite definable family of proper finite selectors both hold.
Definitions may use q, ordinals, and finitely many individual ground-model
sets; the ground model is not supplied as a class predicate.

This settles the Prikry-extension part of final question (ii) in the supplied
synthesis. The key new argument decides a finite pattern before inserting a
point after the deciding condition's stem. The insertion preserves the entire
extension and q but rotates explicitly coded tuples of equivalence classes.

Starting with the least measurable cardinal gives these conclusions and a
normal-measure HOD/Prikry core, while excluding a nontrivial self-embedding of
V_lambda. The augmented package, including that internal normal measure, is
equiconsistent with one measurable cardinal. This is not a claimed lower
bound for finite symmetry by itself.

A further result identifies the minimum size of a nonempty allowed-definable
family of ultrafilters on the particular class q as exactly aleph_0. The
countable family is given explicitly and uniformly from a low-rank free
ultrafilter on the integers.

## Navigation

- Theorem 1.2: main finite-symmetry statement.
- Lemmas 2.1–2.3: cone isomorphism, insertion, and finite-pattern transfer.
- Theorem 3.2: necessity of elementwise fixed points.
- Theorem 4.2: the prior general sufficiency argument, reproved.
- Theorem 5.2: no nonempty finite definable family of selectors.
- Theorems 7.1–7.2: internal normal measure and common Prikry core.
- Theorems 8.1 and 8.4: the sharp local countable ultrafilter threshold.
- Corollary 9.3 and Theorem 9.4: rank-into-rank separation and equiconsistency.
- Section 10: dependency/provenance ledger and remaining questions.

## Scope and proof status

The report supplies mathematical proofs in English. It does not claim
independent peer review, bibliographic priority beyond the supplied research
sequence, or a Lean verification. Classical Prikry preservation and the
Mathias criterion are cited as inputs. The provided Lean project was a
reference and is not modified in this package.

The finite tests check cyclic choice-table orbits, the insertion identity,
the displacement cocycle, and the alternating-block argument. They do not
verify the infinite set-theoretic or forcing arguments.

Two questions remain distinct from the proved results: whether arbitrary
rigidity implies the symmetry conclusions without a Prikry presentation;
and whether a countable definable family of global ultrafilter-valued
kernels exists. A uniform countable local multiselection is not such a family
of global functions.

## Rebuilding

Use a LaTeX installation providing the packages named in the source,
including `newpxtext`, `newpxmath`, and `tcolorbox`. From this directory run:

```text
pdflatex -interaction=nonstopmode -halt-on-error Prikry_Symmetry.tex
pdflatex -interaction=nonstopmode -halt-on-error Prikry_Symmetry.tex
```

The typography and named colors follow the supplied synthesis. Font files
are not included in the archive.

To reproduce the finite checks, with Python 3.9 or newer:

```text
python checks/finite_checks.py
```

The command rewrites `checks/results.json` and raises an assertion on failure.
