# Source164 selected replay

Recover the Source164 archive through the intake placement/recovery map. Set `PACKET` to its extracted `K215_Construction_and_Research_2026-10-21` root and choose a new `OUT` directory. The portable own runner copies it without modifying the recovered input:

```sh
python3 -B run.py --packet "$PACKET" --output "$OUT"
python3 -B review_saved.py --run "$OUT" --packet "$OUT/packet" --output "$OUT/independent-review.json"
```

`run.py` uses only Python's standard library, seven explicit argv vectors and a 60-second wall cap per child process. It invokes no delivery wrapper, manifest suite, ancestor code, broad search, Coq/Rocq or full runtime. It runs the deterministic primary constructor, two forward projection-certificate checkers, the independent context-matrix and raw-code-lift checks, the residual-interface checker, and the reached-frame scanner diagnostic. Original packet files are copied byte-for-byte; no code adapter or source repair was needed. The constructor reads its pinned parent ZIP members as inert data. The selected 29 input identities are captured before and after, with raw stdout/stderr, exits, timing, and all generated output identities.

`review_saved.py` imports no supplied module and executes no candidate. It audits the saved process evidence and the exact expected semantic fields, including canonical table/source bytes and the scanner's endpoint tape difference. After relocation, pass `--packet` naming the recovered unchanged packet; the original actual record stays unchanged and its recorded selected input identities are checked against that explicit path. The first auditor and its receipt are preserved under history; the successor adds only this path override. The seven supplied leaves already have output-path arguments, so the runner itself needs no historical path-only diff.

The full primary runtime is checked once in Source162's separate fresh run. `compare162.py` and `comparison162.json` retain the all-row source-identical state bijection that transfers it to Source164; this is not a new runtime execution. Do not replace that transfer with a claim of equivalence to the earlier accepted215 table, which is not graph-isomorphic.
