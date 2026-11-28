SOURCE AUDIT AND REPRODUCIBILITY

Pinned repository
  VladimirReshetnikov/ProveIt
  Commit: 89d12dd40424f1217fd818d84877b3da52396a3b
  Root tree: 8460c44e1cc4675afbd128f4fce88ab6edfda18c

Recorded subtree identities
  Lean package: 2e133df63d7f4da6b3059c4195324f8e9187ba73
  Lean src:     55fe9c6cb2e5be421c5871e772b6d736ecb5d164
  Proposals:    fe524e84051edf616261f3ed772b0e1abcfaa47e
  Guide:        a3dba62011e45aaf0b2acb79566bedb004fa354e

Versions read from the pinned source
  Lean: leanprover/lean4:v4.35.0
  Mathlib: 56a005855ea17e0b0958f73ec801ae140b0a1679

WHAT WAS ACTUALLY CHECKED

The supplied audit program was run against the local checkout at the stated
commit. It returned PASS, with no errors or warnings. The actual JSON result
is audit_result.json, and the captured console output is audit_run.txt.

1. Recomputed the Git content-tree hashes of the complete Lean src and proposal
   directories from local file bytes, names, and modes. They match the pinned
   trees. Checked the local Git HEAD, root tree, and all four subtree identities.
2. Recomputed 19 proposal text blob hashes and confirmed exact inventory coverage:
   12 TeX sources, 5 README files, and 2 integration plans. All these documents
   were read during the proposal comparison, including future-research sections.
3. Verified 30 selected declaration anchors in 11 Lean source files. Every Git
   blob hash, declaration prefix, exact declaration line, and 1-based line number
   matched. The anchor list was adapted from the local arithmetic-analysis
   source map; each entry was independently checked before inclusion here.
4. Recomputed the Lean src statistics: 803 .lean files, 477,124 LF characters,
   and 477,124 logical lines. All 803 files end with LF. These are source-size
   statistics, not proof-term or kernel-work measurements.
5. Verified the toolchain, lake manifest, and lakefile blob hashes, and read the
   pinned Lean and Mathlib identifiers from their corresponding source files.

The source identity audit does not amount to a line-by-line mathematical review
of every one of the 803 modules. It does not verify Lean elaboration, kernel
acceptance, axiom use, the new four-copy argument, or the global RH theorem.
No new Lean build, independent kernel replay, or Comparator run was performed.

FILES

  revision.json
    Exact repository, subtree, version, file-count, and review-scope metadata.

  proposal_inventory.tsv
    Complete inventory of the 19 reviewed proposal text files, including Git
    blob SHA-1 values and URLs pinned to the stated commit.

  proposal_exclusions.tsv
    Compact comparison of the five bundles. It includes existing future ideas
    as exclusions, not only their proved or worked results. It records why the
    CM norm-cancellation proposal concerns a different local mechanism.

  source_anchors.tsv
    Thirty source anchors, with exact line text and pinned GitHub line URLs.

  audit_sources.py
    Portable audit program using Python 3.10+ and its standard library. Git is
    optional: if a Git checkout and executable are available, the program also
    verifies commit/tree metadata. Without Git, local content and anchor checks
    still run, but the missing metadata check is explicitly reported.

  audit_result.json, audit_run.txt
    Results of the actual successful run for this report.

REPRODUCE

From this directory, run:

  python3 audit_sources.py /path/to/ProveIt --output local_audit.json

The argument is the root of a ProveIt checkout, not the Lean package directory.
The program derives all source paths from the neighboring metadata files; it
contains no assumption about the report-generation workspace. It reads local
sources only, never fetches or downloads, and does not modify the checkout.
Any optional Git subprocess has lazy fetching and transport protocols disabled.

The source directories must match the pinned snapshot. Extra files, changed
executable modes, changed line endings, or edited source bytes can change a
recomputed tree hash. Build outputs outside src do not affect the src digest.

The absence of the new mechanism from the proposal corpus is an evidence-based
comparison of the inspected directory at this commit, not a global priority
claim about the mathematical literature.
