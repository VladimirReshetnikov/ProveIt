Prepared archive helper for committed merged source
aca2a610c9b3722e66e8cf415bca374e9f28cb1a. SOURCE ONLY; NOT EXECUTED.

archive.py differs from the passed merge68ad helper in exactly two literals:
the native-tool directory and the expected source commit. Its algorithms,
receipt-chain checks, exclusive writes, source/artifact guards and failure
behavior are unchanged. common.py, capture.py and run.py remain byte-identical
to the prior native tools. No live helper, repository, source, Git or cache file
was modified by this preparation.

Do not invoke archive.py while a native worker is live or before all three
actual sequential aca2 commands have passed. It requires pinned core, shared
and supplemental receipts, their actual event/log siblings, the source snapshot,
and source ledger; it also rechecks current protected source and fresh combined
artifacts. It writes only a new /tmp archive directory and never runs a checker.
All actual receipt/archive values in this preparation remain unresolved.

The new ledger describes 70 changed owners, 1,386 fewer corpus source lines,
129 removed intermediate names (76 public), retained headers and unchanged
imports. It binds the exact conflict resolution, both comment corrections,
source reviews and actual ordered inventory comparison. The 120 rows and 544
companion occurrences have 27 line-location changes and four whole-object
permutations; this is not a paper-fidelity certificate. The three planned native
commands cover 572 / 1,915 / 351 modules, with 1,964 distinct modules, 1,971
protected inputs and 84 own-root metadata rows. Those rows are not 84 commands.

The previous a879 archive and published cb7319 checkpoint are historical only.
Future NEXT2111, further simplifications and progression drafts remain unapplied
and excluded. Actual original Final closure: 600 modules / 121,788 source lines;
stronger Final: 656 / 135,481. Corpus/core/stronger reductions and the original
Final reduction differ: -1,386 versus -1,320 source lines, respectively.

Root-only usage after all actual evidence is complete (replace every placeholder
with a verified actual SHA256; use a new /tmp output path):

python -B /tmp/gowers-merge04fd-post-native-tools/archive.py \
  --snapshot /tmp/gowers-merge04fd-aca2-source-snapshot.json d33fe17ef5f2f59c3825878f370fbb10b72500e0da1b893b2666bf937480c730 \
  --source-ledger /tmp/gowers-merge04fd-post-native-tools/source-ledger.json SOURCE_LEDGER_SHA256 \
  --core /tmp/gowers-merge04fd-aca2-core-attempt1/receipt.json ACTUAL_CORE_RECEIPT_SHA256 \
  --shared /tmp/gowers-merge04fd-aca2-shared-attempt1/receipt.json ACTUAL_SHARED_RECEIPT_SHA256 \
  --supplemental /tmp/gowers-merge04fd-aca2-supplemental-attempt1/receipt.json ACTUAL_SUPPLEMENTAL_RECEIPT_SHA256 \
  --extra-evidence STATIC_EXTRA_MANIFEST_PATH STATIC_EXTRA_MANIFEST_SHA256 \
  --output /tmp/gowers-merge04fd-aca2-archive-attempt1

Use the exact source-ledger hash from preparation.json. The optional extra
manifest is supplied separately and must contain exact {path, sha256} pairs
under safe labels. Verify actual attempt paths; the command above is a template.

Proposed repository destination after successful staging and root review:
Combinatorics/Ramsey/Research/GowersSzemeredi/verification/2026-10-16-merge04fd-evidence

The helper does not install that destination. Artifact freshness/stability is
mtime/size based, as in the established workflow, not artifact-content hashing.
