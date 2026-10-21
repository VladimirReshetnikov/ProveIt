# Four predecessor-marker presentations of K215

All four tables have 215 working states and an ordinary all-tape halting equivalence to the pinned primary K215, starting in state zero. They do not reduce the state count. The exact role choices 127→124 and 190→160 and their verified compositions are new instances of the inherited conditional-marker technique.

Read `MARKER_PROOF.md` and `independent/review.md`. Native/dense tables, maps and finite proof records are in `marker_family/`.

From this directory:

```sh
python3 -B build_marker_family.py --output /tmp/dr215-markers-fresh
python3 -B independent/audit.py --baseline k215.native.tm --family /tmp/dr215-markers-fresh --corpus marker_family/novelty_corpus --output /tmp/dr215-marker-independent.json
python3 -B verify_marker_corpus.py
```

Use a fresh reconstruction output directory. The first command proves every finite local premise and compares all mapped old-step boundaries through the complete startup prefix; the ordinary induction is in the proof. The second auditor imports no builder code. It independently checks every old transition and incoming-edge invariant, including the special old-176 route. The third checks the frozen 84-graph/321-occurrence corpus.

The original independent audit record was produced on the complete pinned checkout; the portable audit sees the 84 representative table files. Their manifest retains all 321 original occurrences. Both compare the same distinct graphs. The later top-level ZC215 comparison is separate.

The portable `--output` interface was added to the builder for the assembled packet; its produced tables, maps and proof records are byte-identical to the frozen originals. The baseline, architecture and predecessor method remain attributed to ProveIt and its retained notices. The top-level NOTICE and inherited component licenses apply.
