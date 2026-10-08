# Exact LCS after a long common prefix

The manuscript proof is `sections/05_matching.tex`, relative to the archive root.
The implementation changes only `fast/fastunknot/compressed_lcs.py`; four
new tests are added to `fast/tests/test_compressed_lcs.py`. The historical
equal-bigram fallback test in `tests/test_lcs_transitions.py` uses the longer
tail `T^3`, retaining its assertion that the full cut-pair path is exercised.
The original short-tail family is now tested explicitly in the new tests.

## Established result

Given the exact LCP `K` of two SLP words with lengths `K+a` and `K+b`, let
`S=a+b-1`. If `K >= S-1`, all improvements on the common prefix are covered
by the `S` alignments `d=1-a,...,b-1`, at cuts `(a-1,a-1+d)`. Left extensions
are short. Right extensions inside the known shared prefix are exact
small-shift self-comparisons, reducible to finite cycle automata of at most
`S-1` phases. The exact post-LCP cost is `O(g*S^2)` arithmetic/dictionary
operations, `O(S*H)` new grammar nodes, and `O(g*S)` simultaneously live
automaton states. Only at most `5*S-1` seed/tail letters are read explicitly.

The provided implementation uses the conservative fixed gate `S <= 32`.
General compressed LCS remains delegated to the existing complete fallback.
The theorem concerns arbitrary contents of the common prefix, not a promise
of global periodicity. The manuscript distinguishes this new repository
branch from the previously known polynomial-time compressed-LCS result.

`g` counts allocated input grammar nodes, `H` is input height, and `beta`
bounds binary arithmetic and symbol sizes, including numeric caps and
preexisting resource counters. A conservative deterministic
bound for the actual collision-resolving Python dictionary implementation
is `O(g^2*S^3*beta^2)`, in addition to the initial exact LCP. Replacing
dictionaries by balanced comparison maps gives
`O(g*S^2*beta^2*log(g*S+2))` for the same state recurrence. The simpler
`O(g*S^2)` bound is explicitly an arithmetic/dictionary-operation count.

## Reproduction

From the standalone archive root, use a Python runtime with Regina 7.4.1:

```text
python fast/near_prefix_research/benchmark_near_prefix.py --fast-dir fast --output near_prefix_rerun.json
cd fast
PYTHONPATH=.:tests python -m unittest tests.test_compressed_lcs tests.test_lcs_bounds tests.test_lcs_transitions -v
```

The first command works without a git checkout. The driver first attempts
to load the archived LCS source from git commit
`8a95834940cf77cdab1b39571ffc102ca8b6bede`; if git or that snapshot is
unavailable, it automatically reads the sibling `baseline_compressed_lcs.py`.
Both routes require SHA-256
`85061dbf63f3d0af417b5819a0d67d026b70412560d36bbea1fc3faebfdbc412`.
To select the archived source explicitly, run this from the archive root:

```text
python fast/near_prefix_research/benchmark_near_prefix.py --fast-dir fast --baseline-source fast/near_prefix_research/baseline_compressed_lcs.py --output near_prefix_rerun.json
```

The original driver that produced the recorded timings is preserved under
`fast/near_prefix_research/initial/`. The portable driver changes only source
loading and provenance metadata; scientific arms, input construction, seeds,
limits, timing boundaries, and sampling remain unchanged. `source_hashes.json`
records the original driver, portable driver, baseline source, and raw result
hashes. The portability change passed four focused loading/hash checks;
the full timing audit was not rerun or relabeled as a new measurement.

The benchmark has five measured randomized rounds after one excluded warmup,
seed 3103, a two-million-work kernel allowance, and a 100000-node allowance.
Every kernel timing includes complete grammar construction. Raw wall and CPU
times, arm order, statuses, answers, node counts, and work counters are saved.

## Measured results

There are 225 measured whole-knot queries over fifteen inputs and 280 kernel
measurements. All whole queries return UNKNOT, and every case has identical
certificate digests across baseline, A/A control, and new matcher. No whole
query invokes the new branch. Therefore these observations establish
preservation of successful paths, not faster completed knot recognition.

The sum of the small-fourteen median whole-query times is 139.524 ms
baseline, 136.484 ms A/A, and 139.042 ms new. Gordian medians are 1.719,
1.678, and 1.618 seconds respectively; that difference is not attributed
to a branch which never runs. Submillisecond measurements and some longer
controls show shared-environment timing noise; stable work counts are also
reported, and no speedup is inferred from control-only timing differences.

| Family, exponent `N=2^h` | Baseline | A/A | Generic-LCE diagonals | New automaton diagonals |
|---|---:|---:|---:|---:|
| Equal bigrams, h=8 | 4.586 ms | 4.593 ms | 12.073 ms | 1.204 ms |
| Equal bigrams, h=32 | 51.954 ms | 75.993 ms | 219.083 ms | 3.965 ms |
| Equal bigrams, h=100 | 466.427 ms | 447.129 ms | LIMIT | 12.948 ms |
| Equal bigrams, h=500 | LIMIT | LIMIT | LIMIT | 92.580 ms |
| Positive shift, h=8 | 1.970 ms | 1.830 ms | 1.132 ms | 0.118 ms |
| Positive shift, h=32 | 37.794 ms | 46.241 ms | 27.401 ms | 0.450 ms |
| Positive shift, h=100 | 338.582 ms | 321.581 ms | 266.394 ms | 0.819 ms |
| Positive shift, h=500 | LIMIT | LIMIT | LIMIT | 3.515 ms |

At h=500, equal-bigram new work is 116299 units, 6494 nonempty grammar
nodes, and 25691 total evaluated periodic states; positive-shift new work
is 9104 units, 507 nodes, and 1006 periodic states. State counts are totals
over separate tables, not simultaneous memory. The generic-LCE ablation
uses exactly the same alignment reduction but evaluates extensions with
the original compressed prefix/suffix primitives. Its limits show that
the alignment reduction alone does not remove the local comparison cost.

The large-deficit control replaces the twelve-letter saturating tail `T`
by `T^3`. Its `S=73` fails the gate. Baseline, A/A, and new work counts
are identical: 43100 at h=8, 514652 at h=32, and LIMIT at h=100 and h=500.
The interior control is settled by the earlier directed-pair bound;
all arms likewise have identical work counts, including 11103 at h=500.
Neither control supports a new speedup. LIMIT remains a censored incomplete
query and is never a completed-time denominator.

## Scope and further questions

This improves a local exact primitive on supplied compressed words. It does
not bound total group-search moves, intermediate grammar growth, or the
completeness of a shortening search. Doubling relators for a cyclic query
can destroy the small-deficit condition; direct cyclic acceleration is a
separate problem. Useful next questions are an exact cyclic analogue with
one long common arc and bounded exceptional tails, a principled adaptive
deficit gate in terms of reachable grammar size, shared node-phase tables
across shifts, and exploiting already verified non-prefix witnesses while
retaining the finite-cycle reduction.
