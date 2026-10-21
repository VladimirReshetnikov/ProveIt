# Upstream condensed-detachment proposal

Merge `159397838a` adds the research from `4fdc59197a`: a 52-step condensed-detachment derivation, its renderer and untrusted search sources. The eight research files are preserved byte-for-byte. Their reported focused Lean check is upstream evidence, not a new run here.

The eleven adopted Lean sources and all 197 selected module sources retain the phase-nine checked bytes. The four changed Rocq production files retain the exact earlier checkpoint; their proposed replacements remain available in merged Git history. No generator, search program or proof compiler ran for this merge. [merge.json](merge.json) records all thirteen upstream paths and decisions. The [host status note](../../../../../rho8cd/PROVEIT_STATUS.md) separates the delivery README from maintained regeneration.

The 52-step derivation may replace the current implication derivation, which has 82 helper lemmas. A static review is examining a port under the same abstract assumptions and with the existing composition/lifting interfaces. It is not yet adopted or compiled. The smaller single-use inlining candidates remain separately identified.

[Static proof review](source-review/review.md) assesses the generic port. [Independent merge review](merge-peer/review.md) checks the unchanged proof boundary; its record predates staging the reconciled overview and this final wording cleanup. The [saved-packet recheck](postmerge-saved-review.json) still passes after the merge resolution. The earlier phase-nine documentation receipts bind checkpoint `507ccc5db72bd8448347e928016bded6df084d04`; this merge changes its two overview documents only, while all proof and packet bytes remain exact.
