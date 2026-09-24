# Finite symmetry at measurable strength

**Prikry deletion, definable selectors, and countable ultrafilter families**  
Research continuation of `Cardinals4.zip`, prepared 18 September 2026.

## Main deliverables

- `Finite_Symmetry_at_Measurable_Strength.pdf`: the 21-page article, with detailed English proofs.
- `Finite_Symmetry_at_Measurable_Strength.tex`: complete, standalone LaTeX source. The bibliography is included in the source.
- `SOURCE_MAP.md`: exact links between the supplied synthesis and this continuation, including what is new relative to the supplied material and what is not claimed.
- `checks/finite_checks.py`: dependency-free finite combinatorial checks.
- `checks/results.txt`: output of an actual successful run.

## Main mathematical content

In a normal Prikry extension `W[c]` at a measurable cardinal kappa, let `q0` be the finite-change class of the generic sequence, and let `Q_kappa` be the full ambient quotient of cofinal omega-subsets of kappa by finite symmetric difference. Permit ordinal parameters, `q0` as one parameter, and arbitrary fixed ground-model set parameters.

1. There is no nonempty finite definable family of r-out-of-n selectors on `Q_kappa`, for any `0 < r < n < omega` (Theorem 5.2).
2. The exact finite-label classification from the synthesis already holds in this Prikry extension: an equivariant finite-label rule exists precisely when each permutation fixes a label (Theorem 6.2, Theorem 6.4, Corollary 6.5).
3. There is no nonempty finite definable family of ultrafilters on `q0`, but the least size of a nonempty such family is exactly aleph-zero (Theorem 7.1, Theorem 8.2, Corollary 8.3).
4. The universal countable-family construction works at every uncountable cardinal of countable cofinality, without a large-cardinal assumption. The family is naturally a free transitive integer orbit (Theorem 8.2).
5. Adding these conclusions to a normal-trace inner-model configuration does not increase its consistency strength beyond one measurable cardinal (Theorem 10.2).

The new forcing step is finite-observation deletion: pure decision makes a finite observation constant, while deleting one generic point rotates it without changing the extension, ground parameters, or the generic finite-change class. For finite families of selectors, the observation is the *set of finite restriction tables*, not an arbitrarily chosen member of the family.

## Qualifications

These are proof-based proposed results, not independently refereed or formally verified theorems. No literature-priority claim is made. The forcing application answers the Prikry-extension question expressly left open in the supplied synthesis; it does **not** establish the stronger implication from abstract rigidity alone.

The equiconsistency lower bound comes from the explicitly required normal measure in a definable inner model. The report does not assert a measurable lower bound for the selector obstruction in isolation, and does not lower the consistency strength of ultraexactingness.

A countable-valued assignment `q -> U_u(q)` is not a countable family of global ultrafilter-valued kernels. The latter problem is left open.

No new Lean files are supplied or claimed to have been verified. The supplied Lean development was consulted only as a reference to the established interfaces.

## Rebuilding the PDF

A reasonably complete TeX Live installation with `pdflatex`, `newpxtext`, `newpxmath`, `tcolorbox`, and the other packages listed in the preamble is sufficient. From this directory, run:

```sh
pdflatex -interaction=nonstopmode -halt-on-error Finite_Symmetry_at_Measurable_Strength.tex
pdflatex -interaction=nonstopmode -halt-on-error Finite_Symmetry_at_Measurable_Strength.tex
```

An additional pass may be needed after changing pagination. No separate bibliography program, network access, shell escape, or external figure files are required.

The report uses the supplied synthesis's New PX text/math packages, Forest/Olive/Muted/Sage/Pale palette, page geometry, headers, and theorem/callout conventions. Font files are not distributed.

## Running the finite checks

Use Python 3.10 or later, without optimization flags (the checks use assertions):

```sh
python3 checks/finite_checks.py
```

The recorded run checked 193,312 selector tables in 28 cases; 20,523 cyclic stabilizers among 23,590 periodic incidence-word candidates; the six permutations in the five-label example; 32,768 index-cocycle triples; and 2,560 deletion identities, each also checked modulo 1 through 8. All checks passed. These tests do not verify the forcing, HOD, ultrafilter-existence, or consistency arguments.
