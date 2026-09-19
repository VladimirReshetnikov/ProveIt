# Cofinality cascades above strongly compact cardinals

Research continuation of Cardinals3.zip, prepared for Vladimir Reshetnikov,
18 September 2026.

## Files

- Cofinality_Cascades.pdf — 16-page report with detailed conventional proofs.
- Cofinality_Cascades.tex — standalone LaTeX source; bibliography is included.
- PROOF_AUDIT.md — mathematical dependency and scope audit.
- README.md — this file and build instructions.

## Principal theorem

Let V = W[G] be a set-forcing extension of a ZFC ground W. Suppose delta is
strongly compact in V, lambda > delta is a cardinal of V regular in W, and
cf^V(lambda) < delta. Put Theta = (lambda^(+delta))^W, where +delta denotes
delta iterations of cardinal successor, with suprema at limits.

Every forcing presentation over W has a W-antichain of W-size Theta, and
every dense subset belonging to W has W-size at least Theta. More fundamentally,
there are delta increasing W-regular cardinals mu_i > lambda whose ambient
cofinalities tau_i = cf^V(mu_i) are strictly increasing and cofinal in delta.
The mu_i can be chosen no larger than any ground-cardinal bound on the size
of a dense presentation.

The applications cover ordinary exacting cardinals when HOD is a ground, and
gamma-cover-exacting lambda with delta < lambda <= gamma < kappa, where delta
and kappa are strongly compact, using W = HCD(kappa). In the latter case,
covering confines the cascade to (lambda, kappa) and transfers an unbounded
spectrum of cofinality defects to HCD(delta).

These are conditional inconsistency theorems. The report does not claim that
unqualified cover exactingness above a strongly compact cardinal is inconsistent,
does not supply a consistency construction attaining the bound, and does not
claim priority for the combined theorem. Its proofs are not machine-checked.

## Build

A reasonably complete TeX Live or MiKTeX installation is sufficient.
The source uses the same newpxtext/newpxmath families and the Forest/Olive/
Muted/Sage/Pale palette as the supplied synthesis.

From this directory, run:

```text
latexmk -pdf -interaction=nonstopmode -halt-on-error Cofinality_Cascades.tex
```

Alternatively, run the following command three times to resolve the contents,
references, and PDF bookmarks:

```text
pdflatex -interaction=nonstopmode -halt-on-error Cofinality_Cascades.tex
```

There is no external bibliography database, image, Lean dependency, or shell-escape
requirement. Fonts are supplied by the LaTeX installation, not by this archive.

## Provenance and output checks

Input archive SHA-256:
0216098002316082537492ed9638fa1649482c1dd42552fc65b73f1ab1b303b6

The earlier statements used from the input are identified by source path and
section in the report's bibliography. New proofs are separated from those inputs.
The generated PDF was compiled with pdfLaTeX, checked for unresolved references
and overfull boxes, and rendered for visual inspection. The final build log
contained no LaTeX warnings. These document checks are not proof-assistant checks.
