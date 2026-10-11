EXACT HARMONIC-TAIL IDENTITIES
Gap-Four Reconstruction, Hurwitz Shifts, and Alternating Moments
Research continuation prepared for Vladimir Reshetnikov, 11 October 2026

READ FIRST

Harmonic_Tails_Shifts_and_Twists.pdf is the complete article.
Harmonic_Tails_Shifts_and_Twists.tex is its self-contained LaTeX source.
article.tex, sections/, and references.tex are the editable modular source.
All figures in this article are exact mathematical displays and tables;
there are no external image dependencies.

MAIN CONTRIBUTIONS

1. Proof of the optimal-first-q formal moment-rank conjecture for every
   even pair p=q-4, q>=6. The new range relative to the inspected reports
   begins at (8,12). A strict minor-of-order-two comparison theorem holds
   for every even gap, but does not settle all higher determinants.
2. All-order Hurwitz-shifted Bernoulli transforms, an exact discrete
   primitive, the ordinary-sum correction, and all Stieltjes weight jets.
3. A free-shift trigamma-square evaluation and exact formulas for all
   its derivatives at the integral lattice.
4. A signed two-parameter digamma identity, a complete diagonal sign
   matrix, rational-parameter evaluations, a Gamma antiderivative,
   repeated-resolvent derivatives, and colored polylogarithmic primitives.
5. A source-status correction: the centered sixth mixed moment already
   has a harmonic-spectral evaluation. Reduction to a smaller specified
   alphabet remains open.

PROOF STATUS

The infinite-family assertions have mathematical proofs in the article.
The verification programs are finite consistency checks and exact
algebra certificates; they are not substitutes for the all-order proofs.
They use no integer-relation searches. Numerical diagnostics are not
certified interval enclosures. The formal matrix rank is not an assertion
of arithmetic independence of the corresponding zeta values.

Neither the Gaussian S6 nor the revised S8 conjecture is proved here.
The article provides twelve further research questions and identifies
the remaining even-order rank range p>=8, q-p>=6.
The contribution is assessed relative to the inspected repository;
historical priority over the entire literature is not asserted.

REBUILD THE ARTICLE

From this directory, with Python 3.12 or later and a working LaTeX
installation providing latexmk and the packages in the preamble:

    python3 tools/build_article.py

This regenerates the standalone TeX source, runs latexmk in build/,
and copies the final PDF to this directory. The delivered standalone
TeX can alternatively be compiled directly with pdflatex/latexmk.

RUN THE VERIFICATION PROGRAMS

The exact dependency versions used are in requirements.txt. Install
those dependencies in your preferred Python environment, then run:

    python3 verification/verify_gap_four.py --output results/gap_four_exact_results.json
    python3 verification/verify_shifted_tails.py --output results/shifted_tail_results.json
    python3 verification/verify_alternating_master.py --numeric --output results/alternating_verification.json

The alternating program may be run without --numeric for exact symbolic
checks only. The other two programs perform their complete checks by
default. Every assertion failure gives a nonzero exit status.

The recorded checks include 16 gap-four pairs, 1,946 strict negative
minors, two finite telescopers, 168 shifted primitives, 21 inverse
polynomials, 21 rational endpoint tests, 23 derivative coefficients,
144 alternating coefficients, 256 formal endpoint cancellations,
and 52 numerical diagnostics. Detailed rows are in results/.

SOURCE PROVENANCE

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 446dca9bd65c20e409d1d2561d4ffad408103e2a
Commit timestamp: 2026-10-11T05:06:38Z

provenance/source_manifest.json fixes 102 acquired source files by path,
Git blob hash, byte size, and SHA-256. These comprise the manuscript text,
all six current incoming archives and their README, and the preserved
Canonical tail-rank section. The combined manuscript PDF was not needed
for the source audit and is explicitly recorded as not acquired.

provenance/targeted_source_audit.txt specifies the targeted analytic reads.
provenance/proof_status.json separates proved and open claims.
INTEGRATION_NOTES.txt gives the proposed repository updates.
CHECKSUMS.sha256 covers all delivered files except that checksum file itself.

The source inventory and integrity check do not certify every theorem in
the manuscript. The repository was not changed during this work.
