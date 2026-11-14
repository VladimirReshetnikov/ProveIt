# Controller-context contraction searches

These searches found no accepted state identification or redirect.
`summary.json` records their exact scopes. They are bounded discovery
filters, not a lower-bound proof and not part of either accepted machine's
correctness argument.

The primary and cached preliminary collections observe 171 controls outside
the arithmetic box. The final cached collection covers all 194 working
controls, including unary-sweep interiors, generic arbitrary-context list
block traces, all 4,749 source outcomes and the exact blank initialization.
The final collection contains 18,976 symbolic local views. Each view is
expanded to conservative radius-five bit windows; unknown exterior bits
range independently. The recorded `full/patterns_k5.txt` contains the
resulting per-control windows.

From the archive root, the final search can be repeated with Python 3.10+
and a C++17 compiler. Do not disable Python assertions.

```sh
python3 -B search/controller/collect_full.py
g++ -std=c++17 -O3 search/controller/local_merge.cpp -o /tmp/pa_local_merge
g++ -std=c++17 -O3 search/controller/action_merge_all.cpp -o /tmp/pa_action_merge
/tmp/pa_local_merge construction/candidate/pa194C.native.tm 5 300 \
  search/controller/full/patterns_k5.txt
/tmp/pa_action_merge construction/candidate/pa194C.native.tm 5 300 \
  search/controller/full/patterns_k5.txt
```

The first merger tests redirects through existing rows. The second seeks
common replacement first actions whose bounded continuation exactly
reproduces each former action, with restrictions that permit a sound local
identification. A trajectory that leaves the eleven-cell window or exceeds
300 transitions does not provide a witness. Results are empty; stderr
records the controls or choices processed. Candidate discovery would still
require a new complete universal verification.

`collect.py 5` and `collect_cached.py 5` regenerate the two earlier
non-box collections. Their redirect budget was 200 and common-action budget
150. `action_merge.cpp` preserves the corresponding original endpoint
restrictions; `action_merge_all.cpp` allows every working endpoint except
the start. Both and their recorded logs are retained for provenance.
