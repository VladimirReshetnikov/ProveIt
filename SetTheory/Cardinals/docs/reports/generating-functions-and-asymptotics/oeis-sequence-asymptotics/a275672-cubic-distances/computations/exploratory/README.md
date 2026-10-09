# Inconclusive larger-case attempts

These files preserve two budgeted attempts to strengthen the upper
bounds beyond the completed n=7 and n=8 proofs. **Neither attempt
completed its full case split. Neither supplies a global upper bound.**

| Grid | Target excluded if a full run succeeded | Result | Completed cases | Interrupted case |
|---:|---:|---|---|---:|
| 9 | 15 | UNKNOWN after 600.017 seconds | 0–8 of 27 | 9 |
| 10 | 17 | UNKNOWN after 600.106 seconds | 0–3 of 20 | 4 |

The n=9 run used `rainbow_prefix_filtered.cpp`, with 51,920,896 inner
clique calls before its time limit. The n=10 run used
`rainbow_filtered.cpp`, with 29,124,780 inner calls. Outer prefix
enumeration is not included in these counters. Times were observed on
shared hardware.

`MANIFEST.json` records the exact argument vectors, source hashes, logs,
and structured UNKNOWN results. The final report therefore keeps
13 <= a(9) <= 15 and 14 <= a(10) <= 17.

## What the later sources change

`rainbow_filtered.cpp` applies the modulo-four occupancy capacity test
before enumerating geometric edge prefixes for each proposed diameter.
`rainbow_prefix_filtered.cpp` additionally filters candidate counts,
radial color unions, and feasible final parity-class occupancies at
every prefix. The tests are necessary conditions, and their soundness
was independently reviewed. The original n=7 and n=8 proof sources
remain in the sibling `exact/` directory.

From the package root, a longer complete attempt can be started with:

```sh
python3 src/run_exact.py 9 15 --variant prefix-filtered --seconds 3600
```

To inspect or continue a single diameter case, add `--case 9` or another
valid zero-based index. A single-case UNSAT result covers only that
case. A global conclusion requires all diameter cases, with verified
coverage and no remaining UNKNOWN result.
