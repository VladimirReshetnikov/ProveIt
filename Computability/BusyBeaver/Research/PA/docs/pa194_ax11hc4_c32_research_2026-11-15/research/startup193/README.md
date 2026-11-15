# Finite two-edit search for a 193-state initializer

These tables are research cores, **not accepted blank-start consistency
machines**. The inherited 193-state runtime identifies native 301 with 88
and uses `88 0 0 L 51` and `51 0 0 R 122`. Runtime-frame correctness by
itself does not provide a blank initializer.

The pool in `speculative_edits.tsv` has 346 proposals: 327 outside-box
rewrites from the supplied research pool (after excluding unchanged rows
and nine invalid boundary-only proposals), and 19 speculative arithmetic-box
edits. The latter are not assumed semantically correct. `edits.tsv`,
`historical_edits.tsv` and `box_edits.tsv` retain the underlying pools.
Rows contain `id state read write direction_delta target`.

Every pair affecting different transition rows is tested with each of the
193 working controls as initial state. There are 58,485 eligible pairs.
The screen is repeated for append 0 and append 1 at native row `(198,0)`.
The finite limit is 200,000 transitions and absolute head displacement
below 20,000 per run.

Acceptance at native control 84 checks the **entire finite tape support**
against any of the 20 source-frame templates at sites 25 through 44. It
allows arbitrary values in all nine registers, arbitrary translation,
padding at least 48 and any nonempty finite spare list. A physical frame
hit would still need a source-seed proof and validation of every edit.
No hit was found even under this permissive physical criterion.

| Result | Append 0 | Append 1 |
|---|---:|---:|
| Starts | 11,287,605 | 11,287,605 |
| Literal transitions | 1,993,659,748 | 2,173,631,284 |
| Halts | 233,864 | 117,274 |
| Certified outward rays | 11,044,078 | 11,159,792 |
| Bounded and unresolved | 9,663 | 10,539 |
| Complete source-frame hits | 0 | 0 |

The outward-ray certificate follows a closed zero-reading control cycle
that moves monotonically away after the head is outside the one-cell
support. Cells written behind the head cannot affect future reads. Fuel
or head-bound termination is classified separately and is **not** a
divergence certificate. None of these results is a 194-state lower bound.

## Replay

With a C++17 compiler, from this directory:

```sh
g++ -O3 -std=c++17 pair_startup.cpp -o /tmp/pa_pair_startup
/tmp/pa_pair_startup runtime193_append0.native.tm speculative_edits.tsv \
  templates.tsv 200000 /tmp/pa_hits_append0.jsonl > /tmp/pa_result_append0.json
/tmp/pa_pair_startup runtime193.native.tm speculative_edits.tsv \
  templates.tsv 200000 /tmp/pa_hits_append1.jsonl > /tmp/pa_result_append1.json
```

Final JSON receipts, empty accepted-hit files, and progress logs are included.
Wall times will vary; all discrete counts should agree.

The runtime/pool ancestry is the pinned ProveIt PA sub-194 research,
including `Computability/BusyBeaver/Research/PA/docs/pa_sub194_research_2026-11-13`
and the current comparison archive's runtime/bootstrap research. The complete
packet comparison retains exact archive-member identities. Original source
and runtime attribution remain governed by the notices at the package root.
