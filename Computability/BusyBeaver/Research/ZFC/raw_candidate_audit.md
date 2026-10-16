The earlier reordered and shared equality-free `C_P + GIC + IR` candidate has
**255 working states**. Totalizing its sole missing transition and applying the
conservative auditor produces no reduction: all 255 states are graph
reachable, exact step bisimulation has 255 singleton working classes, and the
radius-four local-window search finds no safe single-state merge. This does
not show global minimality. The candidate's consistency calibration is
unresolved, so it is not a new ZFC-consistency machine bound.

The named source table is
`AX-raw_equality_free_C_G_reordered_shared.tm`, SHA-256
`ad84a1c0b78fd89f85228959e048dac9349332196a366420476464a8f0375cb5`.
It has 509 rows. The missing `1.inc/read1` row is filled with
`write1, R, halt`, yielding 510 rows and the same 255 working states. Under
the convention that an undefined transition halts, this preserves halting and
the final tape, while adding a final head move.

`audit_raw_candidate.py` performs this normalization with strict validation,
numbers start as 0 and halt as 255, saves the complete table and name mapping
outside the repository, and invokes `audit_tm.py` with both source and output
hash checks. The canonical complete table has SHA-256
`2374871b8e53b1513c4a13363bff8e8657772a5d7c1926baa24503af15aa388c`.

The measured search checks 24,604 abstract configurations and 64,770 ordered
state pairs at window radius four, permitting at most 64 local steps on each
side of a proposed merge. Its abstraction permits all 510 transition rows.
There is no startup-state reuse. Exact partition refinement stabilizes after
11 rounds with no nontrivial class. The normalizer passes seven regressions;
the conservative auditor passes its eleven built-in tests.

Reproduction, given the generated named input:

```sh
python3 Computability/BusyBeaver/Research/ZFC/audit_raw_candidate.py \
  /tmp/zfc-theory-backend/AX-raw_equality_free_C_G_reordered_shared.tm \
  --expected-sha256 ad84a1c0b78fd89f85228959e048dac9349332196a366420476464a8f0375cb5 \
  --expected-states 255 --scratch /tmp/zfc-raw-candidate-audit \
  --window-radius 4 --macro-steps 64 \
  --output-evidence /tmp/raw-candidate-audit.json
```

The complete evidence is in
[`raw-candidate-audit.json`](raw-candidate-audit.json), including hashes of the
normalizer and auditor. These are executable reduction checks and the stated
normalization argument; no Lean or Coq build, whole-compiler proof, or new
consistency theorem is supplied.
