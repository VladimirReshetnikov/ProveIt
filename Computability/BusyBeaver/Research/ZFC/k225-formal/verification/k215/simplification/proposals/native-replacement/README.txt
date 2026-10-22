K215: reuse semantics instead of repeating transport
Review dated 22 October 2026

Start with report.pdf. report.tex is the full editable LaTeX source.
Review pin: 6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95
Repository: https://github.com/VladimirReshetnikov/ProveIt

Recommendations:
1. Lean: derive quotient Replacement from native quotient collection, with a
   guarded formula and a small partial-functional-image lemma.
2. Rocq: share the common 219/permutation macro proofs using closed-subgraph
   run transport, preserving register files and all exits.

Scope and evidence:
- New formal proposals and GuardedImage.lean / GuardedImage.v are UNCOMPILED.
- No incoming script, generator or proof assistant was run for this report.
- No upstream repository source was modified or committed.
- Upstream component receipts are described as upstream records, not our replay.
- No new machine, net formal source saving, proof-object reduction or speedup
  is claimed.

The new finite mathematical sanity check can be reproduced with:
  python3 check_guarded_image.py
Its recorded output is FINITE_CHECKS.json. It does not verify the syntax adapter,
the quotient implementation or any full machine endpoint.

SOURCE_AUDIT.json contains source URLs, hashes and sizes for the source review.
The Rocq source audit checks syntactic duplication and closed graph footprints
only; formal transport still needs kernel validation. Fetch the four exact
files listed in audit_rocq_macro_footprint.py from the pinned repository, put
them together in a directory, then run:
  python3 audit_rocq_macro_footprint.py --sources /path/to/files --output audit.json
The script rejects bytes not matching the pinned Git blob IDs. No repository
source is executed. rocq_macro_audit.json records the completed audit.

Compile report.tex twice with pdflatex using standard TeX Live packages:
geometry, amsmath, amssymb, amsthm, enumitem, hyperref and fancyhdr.
The font-map declarations accommodate this report's build environment.

SHA256SUMS.json gives hashes of all distributed files other than itself.
No precompiled Lean/Rocq objects, private notes or downloaded executables are
included. Keep the compatibility and endpoint validation caveats in the report
when incorporating the proposals into ProveIt.
