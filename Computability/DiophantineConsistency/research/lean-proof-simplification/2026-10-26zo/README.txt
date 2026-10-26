FURTHER LEAN PROOF SIMPLIFICATIONS FOR DIOPHANTINECONSISTENCY
Prepared for Vladimir Reshetnikov, 26 October 2026

SOURCE PIN
  ProveIt: 9f35798db4a63c25e435fca14d75931144657d7e
  Lean: 4.32.0 (compiler 8c9756b28d64dab099da31a4c09229a9e6a2ef35)
  Mathlib: 81a5d257c8e410db227a6665ed08f64fea08e997

START HERE
  report/report.pdf       Complete report (compiled from report.tex).
  report/report.tex       Self-contained LaTeX source.

FOUR PROPOSALS
  A. One fixed-modulus certificate for all actual Gamma coefficients.
  B. Full LTE divisibility spectrum as the foundational PrimePowerOrder API.
  C. Reset-separated raw-prefix characterization of existing cyclic carries.
  D. A quadratic substitution removes the sixteen_pow_bound induction.

Only B and D have measured production-source savings: 5 + 4 = 9 physical
lines, including the new LTE helper. No source reduction or performance gain
is claimed for the unintegrated Gamma and carry-locality proposals.

LAYOUT
  lean/                   Checked FixedPointCore, GammaCertificate,
                          and ResetLocality source files.
  lte/                    Checked standalone LTE file, complete production
                          candidate, exact patch, metrics, validation logs,
                          portable replay and line-count scripts.
  patches/                Exact PellQuadratic.patch.
  proposals/              Gamma binding sketch (UNCOMPILED) and precise
                          carry-characterization adapter obligations.
  baseline/               Exact original target modules from the source pin.
  scripts/                Standalone-kernel and finite-arithmetic replay.
  evidence/               Numeric certificate, source hashes, receipts,
                          final axiom diagnostics and review notes.
  audit/                  155-entry exclusion ledger, novelty decisions,
                          23-packet/five-archive coverage, source/member hashes.
  MANIFEST.sha256         SHA-256 of every payload file except this manifest.

VALIDATION BOUNDARIES
  - All four standalone Lean kernels compiled with the pinned environment.
  - The exact LTE candidate and all ten existing focused examples passed.
    Six old theorem types and six old axiom sets are unchanged.
  - The Pell replacement has the exact old theorem type and compiled in
    isolation. Its full production module/client graph was not rebuilt.
  - Gamma's universal theorem uses exactly the three existing K-residue
    proposition types. Its repository adapter has NOT been compiled.
  - Carry arithmetic and recurrence-characterization kernels passed.
    The actual ZMod/cell adapter has NOT been compiled.
  - No full repository build, speedup, or new consistency equivalence is claimed.

REPLAY (requires an existing checkout with its pinned dependencies installed)
  python3 scripts/verify_kernels.py /path/to/ProveIt
  python3 lte/verify_lte.py /path/to/ProveIt
  python3 scripts/verify_gamma.py

The first two scripts use `lake env` to select the checkout's environment,
create temporary compiled helper objects, and leave its source unchanged.
They intentionally omit the uncompiled proposals directory. The saved receipts
record the actual isolated compiler runs. See evidence/replay_validation.json
for whether the packaged wrapper was also exercised in this session.

PATCH REVIEW (does not modify a checkout)
  git -C /path/to/ProveIt apply --check /absolute/path/to/lte/prime-power-spectrum.patch
  git -C /path/to/ProveIt apply --check /absolute/path/to/patches/PellQuadratic.patch

BUILD THE PDF
  cd report
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex

The audit assumes every prior idea is already available, including uncompiled,
optional, deferred and alternative proposals. Its 155 entries overlap and are
not 155 independent inventions. Complete filename/member inventories are
separate from the semantic review of primary manuscripts and close precedents.
See audit/COVERAGE.md for the precise scope. Historical manuscript copies and
cached compiled binaries are deliberately not duplicated in this packet.
