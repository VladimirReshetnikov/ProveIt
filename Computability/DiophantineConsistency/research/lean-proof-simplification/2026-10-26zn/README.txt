FURTHER LEAN PROOF SIMPLIFICATIONS — 26 October 2026
=================================================

Start with report.pdf. report.tex and metrics.tex are its complete editable source.

Repository: https://github.com/VladimirReshetnikov/ProveIt
Reviewed commit: e1c8914bc7064d9a8e7c06171a18069a949badd0
Lean: 4.32.0 (8c9756b28d64dab099da31a4c09229a9e6a2ef35)
mathlib: 81a5d257c8e410db227a6665ed08f64fea08e997

FOUR ADDITIONAL PROPOSALS

A. Certify all 941 literal selector rows and the 34 control terms once modulo
   47*2011*120199, then project to each existing modulus. 177 numerical chunk
   certificates become 59. CurrentKernelResidues2011: 843 -> 426 lines (-417).
B. Use x^a=x => x^(a^n)=x in any monoid to unify the three dimension-power
   reductions. CurrentControllerUnits2011: 201 -> 196 lines (-5).
C. Use finite-sum update and pointwise update APIs directly for packed-word
   increment and Boolean-control preservation. CurrentDummyMutation2011:
   193 -> 185 lines (-8).
D. Obtain origin_reflected_zero from reflected_source at h=0.
   CurrentWordOrigin2011: 118 -> 111 lines (-7).

The four patches remove 437 physical lines in the actual pinned source, including
new helpers and retained wrappers. This is NOT a claim of 437 additional lines
in an imaginary tree after every earlier proposal. The exclusion audit treats
all earlier proposal mechanisms as already available, including unadopted ideas.
All 64 existing public declaration headers are retained. The common K residue
adds one public declaration. No speedup or controlled timing comparison is claimed.

STATUS AND IMPORTANT BOUNDARIES

The following supplied isolated Lean files passed the pinned compiler:
  lean/CommonModulusCertificate.lean — exact literal-data numeric certificate;
  lean/PowerFixedPoint.lean — generic monoid law, exact seeds, symbolic wrappers;
  lean/WeightedUpdates.lean — finite update algebra and exact word expression;
  lean/OriginReuse.lean — extracted source dependencies and origin specialization;
  lean/GammaCommon.lean — conditional synthesis of common residue and fixed point.

The combined Gamma fixture keeps the exact radix/B/K residue premises explicit,
retains the natural-subtraction side condition, and allows independent zero
exponents. It is not a fifth measured patch or a production-controller rebuild.

No new supplied proof uses sorry, admit, a custom axiom, or native_decide.
Logs preserve standard-axiom output. The larger common modulus may cost more
per arithmetic certificate. Timing records are descriptive, not benchmarks.

The complete production modules and downstream clients were NOT rebuilt.
The physical-order/permutation/rawWord_cast bridge is retained unchanged in the
common-modulus candidate, but that import closure was not replayed. The power
fixture checks symbolic B under the existing exact residue hypotheses, rather
than replaying its complete production import closure.

Two additional concrete replay candidates are included, clearly unvalidated:
  lean/ControllerPowerComparison.lean
  lean/ControllerPowerAfter.lean
Their earlier attempts stalled in file I/O before diagnostics. They were not
successfully rerun after a small explicit-unfolding edit. They are never counted
among the five successful checks. A historical receipt also mentions an optional
LibraryPowerFixed.lean exploration; it is not needed and is not distributed.

CONTENTS

report.pdf / report.tex / metrics.tex   Complete report and LaTeX sources
lean/                                 Checked cores and two unvalidated extras
patches/                              Four exact unified production patches
proposed/                             Four complete replacement source files
sources/                              Targeted original snapshots and build pins
                                      (NOT a complete clone or buildable project)
audit/                                Exclusion receipts, overlap/rejection ledger,
                                      and independent mathematical/source review
evidence/                             Compiler logs, run receipts, hashes, metrics
scripts/                              Reproducibility helpers
SHA256SUMS                            Manifest of every other distributed file
LICENSE                               Original repository license

REPRODUCE THE NON-LEAN AUDITS

From the extracted packet directory, with Python 3 and git available:

  python3 scripts/verify_artifacts.py
  python3 scripts/audit_common_modulus.py --repository sources

The first checks archive bytes, baseline/candidate hashes, source line counts,
and applies every patch to a temporary copy, verifying exact replacement bytes.
It never edits the real repository. The second audits every literal coefficient,
all old and new numerical chunks, controls, kernel residue, retained bridge and
patch. These are data/source checks, not substitutes for Lean proof checking.

To regenerate the power candidate and ControllerPowerComparison fixture into a fresh folder:

  python3 scripts/build_power_artifacts.py --repo sources --output-dir /path/to/new-output

REPLAY THE LEAN CORES

Use a complete checkout with the exact repository/toolchain/dependency pins and
its mathlib oleans available. No network installation or dependency update is
performed by these replay scripts. From the extracted packet:

  python3 scripts/replay.py --repo /path/to/ProveIt --output-dir /path/to/replay-output

The script checks the pins, resolves the compiler and dependency search path
using lake env, emits PowerFixedPoint.olean before checking GammaCommon, records
commands and logs, and stops on the first nonzero compiler exit. It does not apply
production patches or pretend to have rebuilt clients.

For an already prepared standalone environment:

  python3 scripts/replay.py --lean /path/to/lean --lean-path "$LEAN_PATH"     --output-dir /path/to/replay-output

In this mode, provide all pinned mathlib/dependency library directories yourself.
--show-commands resolves the environment and prints the planned commands without
checking the proofs. --include-unchecked also attempts the two extra concrete
fixtures, which may be expensive. Default replay includes only the five cores.

PRODUCTION INTEGRATION, NOT PERFORMED IN THIS REVIEW

In a clean checkout of the pinned source, review and apply patches in order:

  git apply /path/to/packet/patches/01-common-modulus.patch
  git apply /path/to/packet/patches/02-power-fixed-point.patch
  git apply /path/to/packet/patches/03-weighted-updates.patch
  git apply /path/to/packet/patches/04-origin-reuse.patch

Then the complete module checks, followed by the relevant clients, are:

  lake build DiophantineConsistency.CurrentKernelResidues2011
  lake build DiophantineConsistency.CurrentControllerUnits2011
  lake build DiophantineConsistency.CurrentDummyMutation2011
  lake build DiophantineConsistency.CurrentWordOrigin2011

If earlier proposals are already implemented in your working branch, port the
small logical changes onto that branch rather than expecting patches against a
different baseline to apply cleanly. The report isolates the additional mechanism
of each idea and distinguishes it from existing proposed infrastructure.

BUILD THE REPORT

With XeLaTeX, Latin Modern, DejaVu Sans Mono, and the listed TeX packages installed:

  xelatex -interaction=nonstopmode -halt-on-error report.tex
  xelatex -interaction=nonstopmode -halt-on-error report.tex

The provided PDF has been rendered and visually inspected. It is self-contained;
the TeX file depends only on metrics.tex and normal fonts/packages, not remote data.

AUDIT COVERAGE

All 690 maintained Lean-tree files and all 1,286 research files were verified
against their Git blob identifiers. The five incoming ZIPs were verified, and
SHA-256 hashes were recorded for their 1,042 decompressed members. Main proposal
sections from all 23 rounds a-w and all five incoming reports were read; supporting
notes, prototype files and ledgers were searched for candidate mechanisms. Byte
coverage is not a claim to have read every historical baseline and compiler log
line by line. No general mathematical novelty beyond this scoped source review
is claimed. See audit/ for exact provenance and rejection decisions.
