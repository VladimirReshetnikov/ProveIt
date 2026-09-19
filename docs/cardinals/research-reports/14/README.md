# Cardinals research continuation

## Report

**Small definable sections and stationary-correctness barriers**  
Prepared for Vladimir Reshetnikov, 18 September 2026.

The archive contains a 22-page mathematical research continuation of the two
reports supplied in `Cardinals2.zip`.

- `Cardinals_Continuation.pdf` — compiled report, with detailed proofs.
- `Cardinals_Continuation.tex` — complete, self-contained LaTeX source.
- `PROOF_AUDIT.md` — result map, external dependencies, and limitations.
- `build.sh` — optional three-pass pdfLaTeX build script.

## Main results

1. **Theorem 4.4, page 8:** At an ultraexacting cardinal lambda, every nonempty
   OD_(V_lambda) collection of fewer than lambda complete sections of cofinal
   omega-subsets modulo finite symmetric difference has at least lambda classes
   on which all its sections have fibers of size lambda. The collection need
   not have a definable enumeration. In particular, no nonempty such small
   definable collection of transversals exists.
2. **Theorem 5.1, page 10:** At an exacting cardinal lambda, a small
   OD_(V_lambda) family of subsets of V_lambda is separated by restriction to
   one bounded rank; it belongs to HOD_(V_lambda), which computes its cardinality
   correctly.
3. **Theorem 6.1, page 11:** The new definability profile, together with the
   established low-rank HOD boundary and first-exacting-cardinal property, is
   equiconsistent with ZFC + I0. The underlying ultraexacting/I0 comparison and
   coding theorem are cited existing results, not new discoveries here.
4. **Theorems 7.2, 8.4, 8.6:** A successor-cardinal stationary-set obstruction,
   its stronger chain-condition consequence for a canonical HCD ground, and
   localization of the destroyed stationary set in a lower-completeness core.
   The general Prikry/Solovay nonreflection mechanism is classical; its precise
   use to strengthen the supplied report's ground obstruction is the extension.

## Mathematical status

The proofs are conventional and unrefereed, not proof-assistant verified.
“Extension” means an extension of the supplied archive. Worldwide priority has
not been established. The report does not claim to refute a bare standard
large-cardinal axiom or to settle cover-exacting/strongly-compact coexistence.
The additional hypotheses in each inconsistency statement are essential to the
stated result.

## Building

Use a TeX Live or MiKTeX installation with pdfLaTeX and the packages named in the
preamble, including `newpx`, `microtype`, `mathtools`, `tcolorbox`, `titlesec`,
`fancyhdr`, `hyperref`, and `xurl`.

On a POSIX shell:

    sh build.sh

Alternatively run the following command three times from this directory:

    pdflatex -interaction=nonstopmode -halt-on-error Cardinals_Continuation.tex

No BibTeX run or external graphics are needed. The bibliography is embedded in
the source. No font files are distributed; the source uses the NewPX packages
from the user's TeX installation. Colors and document styling reproduce the
supplied synthesis's forest/olive/sage palette and NewPX typography.

## Production checks

The delivered PDF was compiled with pdfLaTeX in three resolving passes after
editing. The final log contains no warnings, undefined references, overfull or
underfull boxes, or missing-character reports. All 22 pages were rendered and
visually checked; main theorem statements were also inspected at reading size.
These are document-production checks, not mathematical formal verification.
