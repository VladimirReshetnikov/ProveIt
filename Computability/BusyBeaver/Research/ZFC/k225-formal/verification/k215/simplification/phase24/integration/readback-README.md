# Phase24 post-copy readback helper

**Unexecuted source draft.** Root must review `readback.py` before using it.
It reads copied artifact bytes and source/document paths, then writes one new JSON
report. It does not copy files, run proofs or helpers, unpack archives, or access
the network. A PASS establishes post-copy identity and link checks only.

Expected CLI (every path must be absolute):

```text
python3 -B readback.py
  --manifest /absolute/artifact-adoption.json
  --manifest-sha <sha256-of-that-manifest>
  --plan /tmp/k215-phase24-check-v3/candidate-plan.json
  --previous-leaf /absolute/phase23/lean
  --new-leaf /absolute/phase24/lean
  --docs /absolute/phase24/doc1.md /absolute/phase24/doc2.md /absolute/phase24/doc3.md /absolute/phase24/doc4.md
  --output /absolute/new-post-copy-review.json
```

The plan must have SHA-256
`4bda49c298304608bd3196d92a3c748140142e8a649708102d827e690f489505`.
The manifest schema is:

```json
{
  "files": [
    {
      "source": "/absolute/owned/staged/file",
      "destination": "/absolute/canonical/copied/file",
      "sha256": "64-lowercase-hex-digits"
    }
  ]
}
```

Additional top-level metadata is allowed. The list must explicitly include all
copied artifacts, the new eleven Lean leaf files, and the four new Markdown
documents. Duplicate destinations are rejected. Sources must still exist for
comparison. Each source hash is checked, then destination bytes must equal the
source bytes exactly. The output report is generated here, so it is not a copied
artifact entry and must not already exist.

Both Lean leaf directories must contain exactly the usual eleven file names.
The original phase23 leaf bytes must still match their entries among the 102
frozen present pins. All 230 selected source hashes/lengths, 13 canonical candidate
hashes, 102 present pins and sixteen absences are checked directly against the
fixed plan. The output derives observed artifact/link totals; it contains no
hardcoded runtime duration, capture totals or actual-readback result counts.

The four documents must be distinct `.md` files beneath phase24 and adopted by
the manifest. `${` and uppercase whole-word `PENDING` placeholders are rejected.
The helper checks inline Markdown destinations and reference-definition targets
outside fenced code, resolving URL-escaped relative paths against each document.
URL destinations, anchor-bearing targets and absolute targets are excluded from
this local-relative-file-link check. Every included target must be an existing
file. It does not inspect a remote URL or validate anchor identifiers.

No claim is made about proof validity, archive contents, Markdown completeness,
or the accepted terminal receipt. Those retain their separate kernel, actual and
capture reviews. This helper only checks the explicitly described publication
conditions after root has copied the files.

Include all eight changed parent documents as explicit manifest rows. Their copied bytes are checked; the local-link scan covers the four new phase24 documents only. This README expansion changes no reader bytes.
