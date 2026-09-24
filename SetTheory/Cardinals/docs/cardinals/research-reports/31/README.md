# Prikry symmetry and maximal quotient rigidity

Research continuation of the third-edition synthesis in Cardinals4.zip.
Prepared for Vladimir Reshetnikov, 18 September 2026.

## Files

- `Prikry_Symmetry_and_Maximal_Rigidity.pdf`: the 21-page report, with detailed
  English proofs and a comparison with the supplied synthesis.
- `Prikry_Symmetry_and_Maximal_Rigidity.tex`: self-contained LaTeX source;
  the bibliography is included in this file.
- `finite_checks.py`: standard-library-only finite algebra checks.
- `finite_check_results.json`: output from the checks actually run.
- `MANIFEST.sha256`: SHA-256 checksums for the preceding files and this README.

## Main results

The ambient model is V = W[c], where W has a measurable cardinal kappa,
U is a normal measure on kappa in W, and c is ordinary Prikry generic for U.

Theorems 4.2 and 5.3 prove the exact finite-label classification in this model:
an admissible definable map to a finite group action exists exactly when every
individual group element fixes a label. Necessity holds even with arbitrary
ground-model parameters. Theorem 6.2 excludes every nonempty finite definable
family of proper finite-set selectors on the cofinal quotient.

Theorems 8.3 and 9.2 construct 2^kappa distinct rigid quotient classes with
internal measurable HOD cores. A single ground bijection supplies all cores
with the entire V_kappa. The count is 2^kappa in the extension, not only the
ground. Representatives of distinct constructed classes are almost disjoint.
Theorem 10.1 proves simultaneous maximal-width fibres for every ground-definable
complete section. Theorem 10.2 allows finitely many constructed classes as
additional named parameters.

Theorem 11.2 proves that the maximal measurable-tail-core principle, even with
the finite-symmetry and maximal-width conclusions, is equiconsistent with one
measurable cardinal. This is not a consistency-strength claim for the bare
finite-selector obstruction alone.

The finite-word sufficiency construction and least-common-multiple argument
are explicitly attributed to the supplied synthesis. The new ingredients are
the stem-insertion necessity proof, maximal ground coding, and their joint
measurable-strength package.

## Build

With a TeX distribution providing NewPX and the standard packages used by the
source, run these commands in this directory:

    pdflatex -interaction=nonstopmode -halt-on-error Prikry_Symmetry_and_Maximal_Rigidity.tex
    pdflatex -interaction=nonstopmode -halt-on-error Prikry_Symmetry_and_Maximal_Rigidity.tex
    pdflatex -interaction=nonstopmode -halt-on-error Prikry_Symmetry_and_Maximal_Rigidity.tex

No BibTeX, external images, shell escape, or external source downloads are
required. The report uses the NewPX text/mathematics, TeX Gyre Heros headings,
and forest/olive/sage palette of the supplied synthesis. Font files are not
included in this archive.

## Checks performed

The PDF was compiled with pdfLaTeX. The final log had no LaTeX warnings,
undefined references, or overfull/underfull box warnings. All 21 pages were
rendered for visual inspection; the final file was checked for out-of-page
text. Selected full-size pages were inspected after the final layout changes.

Run the finite checks using Python 3.9 or later:

    python finite_checks.py

The executed checks passed for all 873 permutations on one through six
coordinates, with 3,492 insertion comparisons. They also checked the five-label
S_3 action and all 64 binary selector patterns on four points. Under the
four-cycle these patterns form 16 orbits, each of size four.

These are finite sanity checks only. No new set-theoretic theorem was checked
in Lean, and none of the supplied Lean files was modified. The mathematical
proofs are conventional and unrefereed. Novelty is relative to the supplied
synthesis; publication priority is not established.

The results do not establish that abstract rigidity alone implies finite
symmetry, or that every ultraexacting cardinal has 2^kappa rigid classes.
Different classes are not asserted to give different HOD models. Tail measures
are internally complete and are not generally normal.

## Input version

SHA-256 of the supplied `Cardinals4.zip`:

    da3fb1a7c1e5e42af98e1b1f0aa4798829dcca685d312ad70fadac46492dd18d
