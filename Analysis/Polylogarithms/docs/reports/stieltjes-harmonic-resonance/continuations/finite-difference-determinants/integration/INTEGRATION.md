# Proposed integration (no repository edits performed)

Source pin: `73f18ef013d5b74eafc883efb2c15210642df12a`.

Suggested preserved-report destination:

`Analysis/Polylogarithms/docs/reports/stieltjes-harmonic-resonance/continuations/finite-difference-determinants/`

Copy the self-contained package there, retaining modular and standalone TeX,
verification code, result JSON, claim status, and source-scope record. Alternatively,
the ZIP can be placed in `docs/incoming` under the repository's intake procedure.

The direct parent connection is the preserved `determinantal-harmonic-resonance`
report: its further-research questions about repeated rational poles, harmonic
matrix rank, and several residue classes are addressed by Sections 6 and 7.
The single-zeta spectral deformation in Sections 2--5 is distinct from the
moving-denominator Gauss spectral deformation and should not be merged by
identifying their spectral parameters or counterterms.

For eventual canonical integration, natural placements are the harmonic-resonance
material (Sections 2--5), rational/cyclotomic generating functions (Section 7),
and an exact algebra appendix (Section 6). Preserve the distinctions between:

* matrix rank, harmonic determinant degree, and minimal arithmetic depth;
* the normalized ordered sum and its averaged mixed-order polarization;
* the ordinary convergence domain and meromorphic continuation;
* the spectral finite part and the hard-cutoff constant;
* exact critical decay with a nonzero leading coefficient and merely faster decay.

The main source uses ordinary theorem/macro names suitable for a standalone report.
Before inclusion into the canonical manuscript, namespace or adapt its theorem
labels/macros to avoid collisions. No `\input` patch against an uninspected latest
manuscript is supplied, and no assertion is made that the entire canonical book
was rebuilt with this report.

Review `STATUS_UPDATES.md` before changing an open-question ledger. Do not mark
Gaussian S6, revised S8, minimal polylogarithmic depth, or general higher Gauss
resonances as solved by this delivery.
