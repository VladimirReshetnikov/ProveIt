# Prikry symmetry and the finite–countable choice gap

Research continuation of the supplied Cardinals4.zip, prepared for Vladimir Reshetnikov.
Report date: 18 September 2026.

## Files

- `Prikry_Choice_Gap.pdf` — the 21-page report, with detailed English proofs.
- `Prikry_Choice_Gap.tex` — complete, standalone LaTeX source; bibliography is embedded.
- `build.sh` — Unix/macOS build script.
- `build.ps1` — Windows PowerShell build script.

The typography and colors follow `docs/Large_Cardinals_Synthesis.tex` in the input:
newpxtext/newpxmath, Forest #30392C, Olive #687144, Muted #65685F,
Sage #CBD0BC, and Pale #F2F4EB. No font files are distributed.

## Main results

Theorem 1.2: In every ordinary normal-measure Prikry extension W[c], no nonempty
finite definable family of total finite selectors, ultrafilters on [c], or total
ultrafilter-valued kernels exists. The forbidden definitions may use ordinals,
any finitely many ground-model sets, and [c] itself.

Theorem 1.3: A ground-model presentation of names and an ultrafilter on the
natural numbers give countably infinite definable families of total selectors
and kernels. The construction synchronizes the same integer phase over all inputs.

Theorem 1.4: High continuum coding makes the witness families ordinal definable
in a model where no finite family definable from V_kappa exists. The package,
including measurability of kappa in HOD, is equiconsistent with a measurable cardinal.

Theorem 5.1: The exact finite-label criterion from the supplied synthesis holds
in every normal Prikry extension. Its positive half is reproduced from the
supplied work; the new part here is the necessity argument using Prikry symmetry.

## Scope

“New” means new relative to the supplied synthesis. Literature priority has not
been established. These are conventional mathematical proofs, not Lean-verified
theorems or independently refereed results.

The report does NOT claim:
- that abstract rigidity by itself implies the finite-choice obstruction;
- that the countable-family question at an ultraexacting cardinal is settled;
- that the name-presentation parameter has low rank in every uncoded Prikry model;
- that the choice-gap statements alone have measurable-cardinal lower consistency
  strength. The reverse consistency implication uses the explicit HOD-measurability
  clause of the stated package.

## Classical dependencies

The report explicitly imports the standard Prikry property, preservation and
Mathias genericity results; Benhamou's containment-of-generics corollary; set-length
Easton continuum coding; and Silver's consistency of measurability with GCH.
Full references and the exact Benhamou theorem numbering appear in the report.
The new forcing comparisons, finite-family arguments, synchronized countable
constructions, coding interaction, and dependency audit are proved in the text.

## Build

A reasonably complete TeX Live or MiKTeX installation is required. In particular,
install newpx, amsmath, mathtools, microtype, tcolorbox, titlesec, fancyhdr,
booktabs, enumitem, xurl, and hyperref through the TeX package manager.

Run `./build.sh` or `./build.ps1`, or run twice:

    pdflatex -interaction=nonstopmode -halt-on-error Prikry_Choice_Gap.tex

No BibTeX, shell escape, external figures, or downloaded assets are required.

## Verification performed

- The source compiled successfully with pdfTeX/TeX Live.
- Cross-references and bibliography references resolved.
- No overfull-box, missing-character, or undefined-reference warning remained.
- One non-fatal underfull-box warning remains in the bibliography.
- The PDF was rendered and visually checked, including the title, proofs,
  comparison table, and bibliography.
- The supplied Lean files were consulted as references; no Lean compilation or
  formal verification of the new arguments was attempted.
