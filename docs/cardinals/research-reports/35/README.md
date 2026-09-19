# Finite choice and maximal rigidity at one measurable cardinal

A proof-focused continuation of the supplied `Cardinals4.zip` synthesis.
Prepared for Vladimir Reshetnikov, 18 September 2026.

## Contents

- `Prikry_Choice_and_Maximal_Rigidity.pdf`: the complete 24-page report.
- `Prikry_Choice_and_Maximal_Rigidity.tex`: self-contained LaTeX source, including bibliography.
- `finite_checks.py`: dependency-free finite bookkeeping tests.
- `finite_checks_output.txt`: output of the successful test run.
- `Makefile`: optional compilation and test targets.

## Mathematical contributions

The manuscript proves, in every normal Prikry extension of a model with a
measurable cardinal:

1. The exact elementwise fixed-point classification of definable finite-label
   rules, and the impossibility of nonempty finite definable families of
   selectors. The negative statements allow arbitrary ground-model set
   parameters and additional finite-change invariant parameters.
2. The existence of 2^kappa distinct rigid cofinal classes with pairwise almost
   disjoint representatives, encoded in one invariant parameter. Their joint
   hereditary-definability core is contained in the ground, contains V_kappa,
   and carries an internal normal measure on kappa. Every permitted complete
   section has full fibres on this same maximal family.
3. An exact local ultrafilter-choice threshold: finite definable families fail
   at the generic class, while countably infinite definable families exist.
   The positive construction works in ZFC for every cofinal class and has a
   canonical free integer action.

The explicitly stated joint package is equiconsistent with one measurable
cardinal. Its lower bound uses the included internal normal-measure clause;
it is not asserted for the finite-choice classification in isolation.

## Scope and status

All mathematical proofs are in English. Newness is claimed relative to the
supplied synthesis; literature-wide priority has not been established. This
is an unrefereed manuscript, not a machine-checked set-theoretic development.
No new Lean formalization was written or compiled.

The countable ultrafilter construction is local: it is a function assigning a
countable set of ultrafilters to each class. It does not settle the question
about a countably infinite definable family of global ultrafilter-valued
kernels. Nor does the Prikry-model theorem show that the classification follows
from bare rigidity in an arbitrary universe, or that every ultraexacting
cardinal has the maximal rigid family.

## Build

Use a LaTeX installation providing pdfLaTeX, `newpxtext`, `newpxmath`,
`tcolorbox`, and the other standard packages in the source preamble.

```sh
pdflatex -interaction=nonstopmode -halt-on-error Prikry_Choice_and_Maximal_Rigidity.tex
pdflatex -interaction=nonstopmode -halt-on-error Prikry_Choice_and_Maximal_Rigidity.tex
python3 finite_checks.py
```

Alternatively run `make` and `make check`. No bibliography processor or external
images are required. Font files are not bundled.

The PDF uses the supplied report's newpx text/math typography and its Forest,
Olive, Muted, Sage, and Pale colors. The final build had no undefined references
or overfull/underfull box warnings. All pages were rendered for visual checks.

## Computational checks

The recorded run passes 47,454 twist identities, 12,288 phase identities,
1,004 proper-residue-set tests, exhaustive enumeration of 116 selector tables
in 29 orbits, 36 exact input-orbit constraint tests, and checks of 32,640 pairs
of binary branches.

These are finite sanity checks only. They do not verify forcing, HOD,
measurability, infinite cardinal arithmetic, or infinite ultrafilters.
