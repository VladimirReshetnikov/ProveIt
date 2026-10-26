NEW LEAN PROOF SIMPLIFICATIONS FOR DIOPHANTINECONSISTENCY
26 October 2026

START HERE
report.pdf is the complete research note. report.tex and results.tex are its
editable LaTeX sources. The source files, patches and evidence are organized by
proposal rather than by validation environment. No compiled Lean caches are
bundled.

RETAINED PROPOSALS
A. Positive error factor for the two Pell ratio estimates: 77 net lines saved.
B. Arbitrary-premise backward-index synthesis: 10 net lines saved.
C. Successor transport for fork certificates: 3 net lines saved.
D. Projected support-difference theorem: checked, but first use adds 43 lines.
E. Canonical quadratic-pairing witnesses: checked extension, no saving claimed.

The first three changes together save 90 physical lines including all helpers.
Support differences and canonical pairing are staged architectural proposals.
Sign congruence and the graph-depth budget were removed after the final intake
refresh found the same ideas in a newly arrived proposal packet. The exclusion
audit records these overlaps; their candidate code is deliberately not included.

SOURCE AND VALIDATION SCOPE
Lean compilation pin: 7fa06d530df54d4aeb2e18027409df082234c69e
Final repository/intake refresh: 6f46a5e3480a2fa2e45993b8090826f256aeaa56
Lean: leanprover/lean4:v4.32.0
Mathlib: 81a5d257c8e410db227a6665ed08f64fea08e997

Six complete candidate modules compile against the validation pin. The optional
canonical-pairing file imports the actual production predicate and also compiles.
All 54 original public theorem/lemma headers in the five changed existing files
are preserved by whitespace-normalized source comparison. Original and candidate
axiom logs match at the audited Pell and syntax endpoints. No complete 574-file
umbrella rebuild is claimed. Targeted checks reused matching source-verified
project caches and built additional required modules.

All four patches apply cleanly to the final refresh. Only AnnotatedProofChecker
changed between these commits among the retained patch targets: an unrelated
lookup improvement removed eight lines. Applying the variadic patch to latest
preserves that improvement and changes 380 to 370 lines. The full candidate
sources in lean/ are based on the validation pin. For newer main, apply the
patches; do not overwrite its files with these baseline-based complete copies.
No latest-main dependency rebuild is claimed.

LAYOUT
  report.pdf, report.tex, results.tex  Complete report and editable sources
  patches/                            Four independently applicable diffs
  lean/                               Six complete candidate source files
  prototypes/                         Production-importing pairing extension
  baseline/                           Original relevant source snapshots
  audits/                             Lean #print axioms input files
  evidence/                           Receipts, metrics, hashes, novelty audit
  environment/                        Original toolchain and package manifests
  scripts/                            Portable integrity and replay helpers
  MANIFEST.sha256                      Hashes of all other packaged files

REPLAY
1. Use a fresh, complete checkout of the repository at either recorded commit.
   Use its own lean-toolchain and lake-manifest.json. Install the pinned Lean
   toolchain and obtain Mathlib/build dependencies normally. This package does
   not contain dependency caches and does not silently update package pins.
2. Verify this extracted archive:
      python3 scripts/verify_artifacts.py
3. Check the four patches against your checkout without modifying it:
      python3 scripts/replay.py --repo /absolute/path/to/ProveIt
4. To apply them and check the affected module targets in that fresh checkout:
      python3 scripts/replay.py --repo /absolute/path/to/ProveIt --apply --build
   This changes only the explicitly supplied checkout, does not commit/push,
   and records the output in replay-output/. It requires a clean tracked tree.
   Omit --build to apply without compiling.
5. To review one proposal independently, run git apply --check and git apply
   with only its patch from patches/. A Pell application also changes the older
   Diophantine/Paper1980/PellRatio90 module outside DiophantineConsistency,
   because that is the correct shared dependency level.

Manual targeted build after applying all patches:
  lake build +DiophantineConsistency.NativeHalfBinomial \
    +DiophantineConsistency.AnnotatedProofChecker \
    +DiophantineConsistency.AnnotatedSyntaxGraphs \
    +DiophantineConsistency.NativeTemporalSupport54

From the repository directory, lake env lean can then check the absolute paths
of the four files in audits/ and prototypes/CanonicalPairingIntegration.lean.
Successful replay on a different commit is additional evidence; it is not implied
by the recorded baseline compilation receipts.

PDF REBUILD
With a normal TeX Live installation containing the packages listed in the source:
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
  pdflatex -interaction=nonstopmode -halt-on-error report.tex
A third pass may be useful after structural changes. The original PDF was rendered
and visually reviewed. Rebuilding changes its hash; integrity verification then
correctly reports a difference from the distributed original.

NOVELTY SCOPE
The initial seven ZIPs and the already-retired directly linked manuscript were
compared with three ZIPs added during the final refresh: ten ZIPs, 2193 inventoried
members, eleven primary manuscripts in total. Novelty means absence of an
equivalent mechanism in this inspected corpus, not priority in the literature.
The 606 obstruction, generic fragment composition, product-equivalence projection,
and generic canonical-witness philosophy are not claimed as new. The report states
the specific additional interface in each retained proposal.
