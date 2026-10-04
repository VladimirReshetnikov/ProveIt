# Independent counting review

`REVIEW.md` is a source-bound mathematical review of the frozen encoded-gap counting continuation. Verdict: ACCEPT within the stated scope; no required correction found.

`check_independent.py` is a separate Python 3.9+ standard-library checker. It does not execute, import, or modify any source-packet program. It derives primitives from reduced rational denominators and supplements the proof review with exact finite arithmetic.

From this directory, replay with:

```sh
python3 -I -B check_independent.py ../native-gap-counting-continuation-20261004 > checks.replay.json
cmp checks.json checks.replay.json
```

The input directory can be anywhere. By default the dependency proof is expected at the sibling `native-gap-halting-continuation-20261004/PROOF.md`; pass `--dependency /path/to/PROOF.md` to override it. Source hashes are pinned, and all manifest entries are verified. Redirect output only outside the frozen source directories.

`checks.json` records the completed independent run. `MANIFEST.json` binds this review's artifacts. The copied isolated replay is documented in `portable_replay.txt`.

All counts concern encoded positive integer triples. They are neither halting-input counts nor witness counts, and no OEIS open-problem claim is made.
