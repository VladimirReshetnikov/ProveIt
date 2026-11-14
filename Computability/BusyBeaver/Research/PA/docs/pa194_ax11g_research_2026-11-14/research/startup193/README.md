# Exact blank-start replay of the physical 193-control trials

The pinned corpus contains 53 spanning graph classes with 193 controls.
One uses the inconsistent coefficient-three numerical calculus. Its logical
rejection is documented in the pinned repository at
[`pa194nq_research_2026-11-13/search/factor3_obstruction`](https://github.com/VladimirReshetnikov/ProveIt/tree/32d0d8b7d93a63ad4106c18cdb29b37927acdad2/Computability/BusyBeaver/Research/PA/docs/pa194nq_research_2026-11-13/search/factor3_obstruction).
That separate logical certificate is attributed and is not rerun here.

This directory contains all 52 remaining physical trial tables and the
fresh results of starting each one from every existing working control on
an all-zero tape. The replay has 52 × 193 = 10,036 cases:

| Outcome | Cases |
|---|---:|
| Finite halt | 106 |
| Certified outward ray | 9,930 |
| Unresolved or fuel exhausted | 0 |

Every case reaches its certificate in at most 117 transitions. A ray
certificate requires an exact zero-reading self-loop moving into an
entirely blank half-line. The row may write behind the head; by induction,
every subsequent scanned cell is still zero and the same row applies.
This is an infinite-run proof from a finite invariant, not a timeout.

Run, from the package root:

```sh
python3 -B research/startup193/verify.py
```

The script independently reruns the literal transitions and compares every
saved endpoint and half-line condition in `certificates.json.gz`, which
retains the complete certificates without loss. `manifest.json` binds every
table to its exact bytes, source path, and graph class. The saved replay
summary is `verification.json`. Add `--receipt /tmp/startup193.json` to keep
a separate fresh receipt.

The original runtime193 fold and its relatives can have correct behavior
on initialized source frames while failing on the blank tape. These cases
show why a source-runtime contract cannot replace initialization. The
classification concerns only the displayed 52 graphs; it is not a lower
bound for arbitrary 193-state Turing machines or other bootstrap edits.
