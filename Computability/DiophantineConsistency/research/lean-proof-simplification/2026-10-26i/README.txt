EIGHT ADDITIONAL LEAN PROOF SIMPLIFICATIONS
ProveIt / DiophantineConsistency — 26 October 2026

START HERE
  report.pdf       Complete report
  report.tex       Corresponding LaTeX source

Reviewed ProveIt commit: e73fa2e916c9bb6f61c79e4fe2cd02b5f43e9d11
Lean: 4.32.0
Mathlib: 81a5d257c8e410db227a6665ed08f64fea08e997

RESULTS
Eight mechanisms were screened against both current incoming entries and the
explicitly referenced earlier simplification packet, including supplementary
notes. Six concrete refactorings supply exact patches across seven production
files, reducing their total physical source from 2501 to 2392 lines (109 fewer).
Two checked foundations concern Primrec/fun_prop and carry uniqueness; no net
production line saving is claimed for those two.

MECHANISMS
1. Preserve the chosen rational roots when proving they are integers.
2. Extract unit factors from the complete product once.
3. Prove one exact tree-decoder graph with a quote/depth product invariant.
4. Recover invariant predecessors using finiteness and injectivity.
5. Obtain out-of-range coefficient zero from a factor-degree envelope.
6. Derive rotation from convolution with a point mass.
7. Register Primrec with compositional fun_prop rules.
8. Prove fixed-digit carry uniqueness by a finite maximum argument.

VALIDATION LIMITS
Complete patched modules checked: NearSquareFinalizer, MarginFinalizer,
ShortSystem, NativeFieldCycles2011, NativeCyclicRotation.
Complete original modules also checked for the finalizer pair, field cycles,
and rotation, with matching audited axiom sets.
Decoder: complete affected Tree submodule checked, with all original Tree
public declarations retained; full enclosing checker module not rebuilt.
SelectiveCarry: exact replacement declaration checked against the actual
original encoding modules; full packing-dependent module not rebuilt.
All eight mechanism examples compile. Audited axioms are subsets of propext,
Classical.choice, Quot.sound; no sorryAx appears in the delivered checked
results. No full ProveIt downstream build or performance speedup is claimed.

BUILD THE STANDALONE EXAMPLES
From this extracted directory, with elan/Lake installed:
  lake update
  lake exe cache get
  lake build RefactoringExamples
The package pins Lean and Mathlib. The first two commands obtain dependencies;
the build can then be repeated with:
  bash scripts/replay.sh

The three unchanged upstream encoding modules under
lean/DiophantineConsistency are included solely to make SupportEnvelope
replayable. They retain their upstream definitions and proofs. Their hashes
appear in evidence/source-inventory.csv. Other examples are self-contained
against Mathlib; they do not import the full ProveIt development.

REVIEW THE PRODUCTION PATCHES
Check an existing checkout without changing it:
  python3 scripts/check_patches.py /absolute/path/to/ProveIt
This first checks every touched file against its recorded SHA-256, then runs a
combined git apply --check from that checkout. The combined patch contains all
seven file changes; NearSquareFinalizer and MarginFinalizer apply together.

After reviewing, apply from an isolated checkout:
  git apply /absolute/path/to/this/package/patches/all-proof-refactorings.patch
Then rebuild the affected modules and the downstream library. The package
provides originals/ and proposed/ for direct comparison. No patches were
pushed or applied to the user's remote repository during this review.

REBUILD THE REPORT
Requires XeLaTeX, latexmk, fontspec, unicode-math, fvextra, and standard LaTeX
packages, plus Latin Modern and DejaVu Sans Mono fonts:
  bash scripts/build_report.sh

EVIDENCE
  evidence/patch-metrics.json             Exact production counts and hashes
  evidence/source-integrity.json         All 570 reviewed Lean files verified
  evidence/source-inventory.csv          File-by-file lines and content hashes
  evidence/candidate-novelty-crosswalk.json
  evidence/exclusion-catalog.json        32 earlier proposal families
  evidence/incoming-index-scan.json      Entire 1952-line index scan record
  evidence/*/                           Detailed validation records and logs
  notes/                                Expanded reasoning and adoption notes
  SHA256SUMS.txt                         Delivered file checksums

Novelty is relative to the audited proposal set, not a claim that established
mathematics or Mathlib lemmas are globally new. The full historical construction
papers linked transitively by the incoming index were not all reread. The
complete index and both simplification manuscripts were reviewed.
