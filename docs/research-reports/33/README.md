# Finite definable choice from one measurable cardinal

Research continuation of the supplied Cardinals4.zip archive, dated
18 September 2026. Prepared for Vladimir Reshetnikov.

## Files

- `Prikry_Finite_Symmetry.tex`: complete standalone LaTeX source, including references.
- `Prikry_Finite_Symmetry.pdf`: compiled report with detailed English proofs.
- `finite_checks.py`: deterministic standard-library Python checks of finite algebra.
- `finite_checks.txt`: output from the supplied script.
- `README.md`: this document.

## Main result

Let W satisfy ZFC and let U be a normal measure on kappa in W. In the normal
Prikry extension V = W[c], with q_* = [c] modulo finite symmetric difference,
there is no nonempty finite family of proper finite-subset selectors on
Q_kappa that is ordinal-definable from q_* and any fixed ground-model set
parameter. More generally, finite equivariant label problems have such a
finite family exactly when every individual permutation fixes a label;
then one low-rank-parameter-definable rule exists.

This supplies the Prikry-model counterpart explicitly asked for in the
source synthesis. The argument uses same-universe finite-tail recoding and
finite sets of evaluation tables, not an ultraexacting embedding and not
a definable choice of one member of a finite family.

Additional results: relative clopenness of definable traces; full phase and
coordinate saturation; and an exact countable threshold for definable local
families of ultrafilters on the full power set of the generic tail class.

## Scope

The proofs establish a construction from one measurable cardinal. They do
not prove that abstract rigidity alone implies all the new finite-choice
conclusions. The countable ultrafilter construction gives a countable-valued
correspondence, not a countable definable family of global kernels.

The report separates classical inputs, arguments inherited from the archive,
and the new forcing applications. Worldwide publication priority has not
been established. The English set-theoretic proofs are not Lean-verified.
The finite checks neither verify forcing nor certify infinite-cardinal
arguments. No new lower consistency bound is claimed.

## Rebuild

Use pdfLaTeX with newpxtext, newpxmath, the AMS packages, microtype,
tcolorbox, titlesec, fancyhdr, geometry, enumitem, booktabs, tabularx,
xurl, and hyperref (normally available in a full TeX Live installation).

    pdflatex -interaction=nonstopmode -halt-on-error Prikry_Finite_Symmetry.tex
    pdflatex -interaction=nonstopmode -halt-on-error Prikry_Finite_Symmetry.tex

Run one further pass if cross-references request it.

The source adopts the font configuration, geometry, Forest/Olive/Muted/Sage/Pale
palette, theorem treatment, and box styling of the supplied synthesis.
No font binaries are included.

Run the finite checks with Python 3.10 or newer:

    python3 finite_checks.py

All checks are bounded, deterministic, and require no external package.
