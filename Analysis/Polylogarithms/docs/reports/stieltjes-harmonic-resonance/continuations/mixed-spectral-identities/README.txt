MIXED SPECTRAL IDENTITIES
Harmonic Newton Series, Dougall Jets, Unequal Twists, and Stieltjes Collisions
10 October 2026

This package is an additive research continuation prepared for ProveIt.
The article contains ordinary analytic proofs, explicit domains, source
corrections, numerical diagnostics, and twelve further research questions.
It does not claim a proof-assistant formalization or global literature
priority. The retained Gaussian S6 and current S8 candidates remain open.

READING AND BUILDING

The main PDF has 40 pages, including the title and contents pages.
The standalone source and PDF share the basename:
    ProveIt_Mixed_Spectral_Identities_2026-10-10

article.tex is the modular source. Its inputs are in sections/ and
references.tex. The standalone .tex contains those inputs inlined and can
be compiled by itself. Regenerate it after editing the modular sources with
    python code/build_standalone.py
Both use only standard TeX Live packages; no external
image, bibliography processor, network access, or shell escape is required.

From this directory, build the modular source with:
    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

Or compile the standalone source with:
    latexmk -pdf -interaction=nonstopmode -halt-on-error ProveIt_Mixed_Spectral_Identities_2026-10-10.tex

The inspected build used pdfTeX 1.40.25 (TeX Live 2023/Debian) and latexmk
4.83. The final TeX log had no warnings, unresolved references, or overfull
or underfull boxes. Rendered pages were visually inspected.

COMPUTATIONAL REPLAY

Use Python 3.11 or later with mpmath 1.3.0 and sympy 1.14.0; exact installed
versions for the supplied run are recorded in results/environment.json.

Install dependencies into your chosen environment if needed:
    python -m pip install -r requirements.txt

Run all four scripts:
    python code/run_all.py

Or run one:
    python code/verify_harmonic.py --output results/harmonic.json
    python code/verify_dougall.py --output results/dougall.json
    python code/verify_twists.py --output results/twists.json
    python code/verify_collisions.py --output results/collisions.json

The scripts contain fixed test inputs and write results relative to this
package by default. They need no repository checkout or network access.
The high-precision harmonic and collision computations may take several
minutes. run_all.py stops if a script raises an assertion or returns a
nonzero exit code; it also writes results/replay_summary.json.

INTERPRETING THE COMPUTATIONS

Harmonic: 26 numerical checks, including 240-term Newton truncations at
180 working digits. Truncation discrepancies are about 1e-18 to 1e-15;
180-digit arithmetic is not a claim of 180 correct digits in a truncation.

Dougall: 13 numerical comparisons, 6 exact Bell-polynomial checks, and
21 exact polynomial residue-grid checks. Explicit finite asymptotic tails
are diagnostics, not certified error bounds.

Twists: 51 exact assertions (49 partial-fraction rows, a corrupted-sign
rejection, and one jet polarization identity), plus 18 numerical checks.

Collisions: 17 separated-collision diagnostics, a two-split merged-moment
calculation, and the finite anomaly. At a positive collision parameter
the asymptotic residual is nonzero; the theorem predicts its limiting
order, not exact equality of the truncated expansion.

The article supplies the proofs. No numerical record is an interval
certificate for an infinite identity or an arithmetic independence result.

REPOSITORY PROVENANCE AND INTEGRATION

Repository:
    https://github.com/VladimirReshetnikov/ProveIt
Inspected commit:
    dcd95baeb7c0e914b138bddef6829c5b1d52b726
Inspected locations:
    Analysis/Polylogarithms/docs/manuscript
    docs/incoming

All six incoming archives at that snapshot were inventoried; the relevant
mathematical sections were inspected. This is a targeted research audit,
not a claim to have checked every line or certificate in the repository.

integration/integration_notes.txt maps the additive results and their
labels to the earlier reports. integration/claim_status.json gives a
machine-readable status table. integration/proposed_source_corrections.patch
contains two narrow canonical-source edits. It was checked with git apply
--check against the pinned snapshot and has not been applied to the repo.

The ZIP contains this complete package. Prior source archives, build-cache
files, and transient PDF-render images are intentionally not duplicated.
