FOUR COPIES SUFFICE FOR LOCAL THETA SHARPNESS
CM norm cancellation in the Alpöge–Claude proof of RH and Dirichlet GRH
Analysis date: 27 November 2026 (America/Los_Angeles)

MAIN RECOMMENDATION

Use local CM norm pairs instead of squares of rational p-adic scalars in
the cancelling theta product. Two copies suffice at unramified primes;
three suffice at the ramified prime, where near pairs are absent.

Combining the existing generic coupling calculation and residual witness
arguments gives the same local bound as Data.leastValLE_twelve with four
copies:

    v_p(l!) + val_4(l) <= S_p + 2 sum_tau v_p(B_tau).

All hypotheses, S_p and B_tau are retained exactly. The safe first
implementation derives the current twelve-copy interface by adding eight
degree-zero copies. A subsequent optional geometric change must preserve
the total ambient theta-lift rank 2z.

STATUS — PLEASE RETAIN IF FORWARDING

The report contains a paper-level mathematical derivation from explicitly
identified existing source lemmas. The source and proposal inventories
were inspected, and the provided exact finite checks and offline source
audit were actually run.

The Lean candidate is NOT compiled, elaborated, or kernel-checked. It
contains four basic candidate lemmas, not the complete local selectors or
the four-copy theorem. Its lack of sorry/admit/axiom declarations does not
imply formal verification. We did not rebuild or kernel-replay the
original 803-module proof; the report separately identifies external
verification results for the matching original source tree.

GRH here means GRH for Dirichlet L-functions. No broader automorphic or
Artin GRH result is asserted. Novelty is relative to the user's specified
proposal corpus at the pinned revision, not a priority claim against all
mathematical literature. No total build-time or whole-proof size saving
has been measured.

PINNED BASELINE

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit:     89d12dd40424f1217fd818d84877b3da52396a3b
Project:    Analysis/GeneralizedRiemannHypothesis/Lean/grh
Lean:       leanprover/lean4:v4.35.0
Mathlib:    56a005855ea17e0b0958f73ec801ae140b0a1679
Lean src:   803 files, 477124 lines including comments and blank lines
Src tree:   55fe9c6cb2e5be421c5871e772b6d736ecb5d164

CONTENTS

report.tex / report.pdf
    Full source-grounded analysis, mathematical proof, exclusion audit,
    implementation stages, verification boundaries, and bibliography.

lean/NormPairCancellation_UNCOMPILED.lean
    Candidate norm-balanced product, two-factor unit and padding lemmas.

lean/INTEGRATION.txt
    Exact formalization tasks, required local selectors, generic-copy
    interfaces, the safe twelve-copy compatibility route, and optional
    migration of the actual derivative block.

lean/LICENSE / lean/NOTICE / lean/ATTRIBUTION.md
    Exact upstream license and attribution files for adapted Lean source.

checks/check_norm_cancellation.py
    Python standard-library exact checks, no network access.
checks/checks.json / checks/checks.txt / checks/README.txt
    Recorded witnesses, actual output, methods, and finite-check scope.

sources/revision.json
    Commit, tree hashes, pinned versions, counts, and verification scope.
sources/proposal_inventory.tsv
    Audited 19 documents: 12 TeX sources, 5 READMEs, 2 integration plans.
sources/proposal_exclusions.tsv
    All five existing bundles, including future-work exclusions.
sources/source_anchors.tsv
    Thirty selected declarations, exact lines, blob hashes, pinned links.
sources/audit_sources.py
    Portable offline Git/content/declaration audit.
sources/audit_result.json / sources/audit_run.txt / sources/README.txt
    Recorded audit results and reproduction details.

SHA256SUMS
    SHA-256 checksums for every other delivered file.

REPRODUCE THE PDF

From this extracted directory, with a standard TeX installation:

    latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex

The document uses ordinary LaTeX packages and embedded vector fonts.
It was compiled with pdfTeX/TeX Live and all pages were rendered for
visual review. The archive omits auxiliary compilation files.

REPRODUCE THE EXACT CHECKS

Python 3.10 or newer is sufficient; no third-party Python packages:

    python3 checks/check_norm_cancellation.py --output checks/reproduced.json

Recorded run:
    61 inert cases
    55 split cases (including 8 at p=2)
    8 ramified cases
    Total: 124 local cases
    Odd-prime precision p^7; split-at-two precision 2^12
    6 formal-series identities through degree 10, with nonzero controls

These are finite sanity checks, not a proof of p-adic convergence or of
the formalized RH development.

REPRODUCE THE SOURCE AUDIT

Obtain a local ProveIt checkout with the three requested source/guide/
proposal directories at the pinned revision, then run:

    python3 sources/audit_sources.py /path/to/ProveIt --output local_audit.json

The script never fetches missing Git objects or contacts the network.
The supplied audit passed without warnings or errors.

ATTEMPT THE LEAN CANDIDATE

Use the pinned project with its dependencies built. From its grh directory:

    lake env lean /absolute/path/to/lean/NormPairCancellation_UNCOMPILED.lean

This command is an outstanding validation step, not a recorded success.
Read lean/INTEGRATION.txt before attempting broader changes.

CHECK ARCHIVE CONTENT INTEGRITY

From the extracted directory on systems with sha256sum:

    sha256sum -c SHA256SUMS

ATTRIBUTION

The proof is Levent Alpöge's, with Claude, as credited by the upstream
project. This analysis and proposal were prepared with OpenAI assistance.
The candidate adapts proof structure from upstream Apache-2.0-licensed
source; preserve the included license and notices when reusing it.
