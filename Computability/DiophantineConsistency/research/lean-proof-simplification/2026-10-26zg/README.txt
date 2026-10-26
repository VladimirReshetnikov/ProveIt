FOUR FURTHER LEAN PROOF SIMPLIFICATIONS
ProveIt / Computability / DiophantineConsistency
Prepared for Vladimir Reshetnikov, 26 October 2026

Start with report/report.pdf. Complete editable LaTeX is in report/.

SCOPE
Source/compiler baseline: 89226e3921bce3e8949fadd12d3efb6914c7630c
Closing novelty review:   7df43cdfacb490cd3ca3acd23e39027efebf8801
Repository: https://github.com/VladimirReshetnikov/ProveIt
Lean: 4.32.0 (8c9756b28d64dab099da31a4c09229a9e6a2ef35)
Mathlib lock: 81a5d257c8e410db227a6665ed08f64fea08e997

All target files were unchanged in the closing GitHub comparison. The initial
653-file maintained Lean source set was byte-verified against Git blob hashes.
The closing refresh was a bounded change/novelty review, not a fresh whole-project
source review or build. No full project build or speedup is claimed.

NOVELTY BOUNDARY
The 23 placed proposal packets (2026-10-26a through w) and all five incoming
ZIPs at the closing pin were audited as prior work, including optional and
uncompiled proposals. No matching mechanism was found for the retained four
families in those 28 directly audited packets. This is a bounded exclusion
claim, not a claim of global mathematical originality. See the report and
evidence/exclusion_catalog.json. A coprime-divisibility candidate was withdrawn
after the fifth incoming ZIP appeared; its proposed code is not included.

WHAT IS CHECKED
P1: Polynomial identities transport split-zero semantics over every additively
    cancellative commutative semiring. The core, literal conditional selection
    row with exact input slots, and Boolean noncancellation counterexample all
    compile against rebuilt current lower production dependencies. Full
    ObjectConditional/internal-model integration was not compiled. The core
    adds 72 physical source lines including comments and audit print commands;
    no immediate net line reduction is claimed.
P2: Complete original and proposed SyntaxCoefficients modules compile. The
    candidate is 110 lines versus 120, including its helper and added import.
    Five list inductions become one. Executable definitions are preserved.
P3: Environment restriction/quantifier kernels compile. The ObjectPolynomial
    patch proposes 20 -> 8 declaration lines, but the full production module
    WAS NOT COMPILED. It remains an integration-pending proposal.
P4: Exact old and new width_dvd_exponent declarations compile with unchanged
    signature and axiom dependencies (12 -> 8 lines). The full enclosing
    NativeBinaryScale module was not rebuilt. Optional prime/block-radix
    classification prototypes compile but are not counted as further savings.

The figures 10, 12, and 4 have different validation scopes. They are not a
verified global 26-line saving, and exclude the added shared P1/P4 APIs.

CONTENTS
report/       PDF and all TeX sources.
lean/         Checked prototypes, exact declarations, and counterexample.
patches/      Three proposed production edits.
baseline/    Exact production sources for those edits.
candidates/  Complete proposed modules (the latter two remain uncompiled).
evidence/    Compiler logs, source hashes, line counts, exclusion ledger,
             candidate decisions, and closing GitHub comparison.
scripts/     Integrity verification, targeted compiler replay, report build.

REPRODUCTION
1. Extract this ZIP. Check its unmodified contents:
     python3 /path/to/packet/scripts/verify.py
   This verifies integrity and source hygiene, not Lean correctness.

2. Use a complete disposable checkout at the source or closing pin, with its
   locked Lean/Mathlib dependencies already fetched and built. The packet
   intentionally does not distribute toolchains, caches, or the whole repo.
   From the repository root, run:
     lake env python3 /path/to/packet/scripts/replay.py --repo . --work /tmp/proveit-replay
   The work directory must not already exist. Replay verifies recorded source
   hashes, rebuilds the four lower production modules, checks six prototype
   files, and checks both complete sparse-coefficient modules. It writes new
   compiler receipts under --work. It does not patch the checkout or run a
   complete object-model build. Use Linux, macOS, or WSL with Python 3.

3. To assess production integration, first review the chosen patch, then use a
   disposable checkout, for example:
     git apply --check /path/to/packet/patches/environment-restriction.patch
     git apply /path/to/packet/patches/environment-restriction.patch
     lake build DiophantineConsistency.ObjectPolynomial
   Rebuild relevant direct clients/check modules too. The analogous targets
   for the other two patches are DiophantineConsistency.SyntaxCoefficients
   and DiophantineConsistency.NativeBinaryScale. These production integration
   commands are instructions for further checking, not recorded successes.

4. To rebuild the PDF:
     python3 /path/to/packet/scripts/build_report.py
   Requires XeLaTeX; Bitstream Charter, DejaVu Sans, and DejaVu Sans Mono fonts;
   and standard TeX packages geometry, fontspec, amsmath, amssymb, mathtools,
   booktabs, longtable, array, enumitem, xcolor, fancyhdr, titlesec, fvextra,
   hyperref, and xurl. No installer or network action is invoked by the script.
   Rebuilding produces auxiliary files and can change PDF hashes/metadata.

READING THE EVIDENCE
The report and source-provenance.json are the final integrated account.
semantic-findings.md and arithmetic-findings.md provide supporting research
notes, reconciled to the final 28-packet audit. Logs retain original local
source paths as provenance.
Elapsed times are receipts, not reliable performance benchmarks.

ATTRIBUTION
Baseline source and edited source excerpts originate in Vladimir Reshetnikov's
ProveIt repository. Pinned source URLs and SHA-256/Git-blob identities are in
evidence/source-provenance.json. Mathlib interfaces use the repository's lock.
