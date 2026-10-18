# Worklist generators

These scripts reproduce the computations that produced the numerical guard
invariants. They use only Python's standard library and the pinned literal
source at `../reference/Prog254.v`. They neither import nor modify the separate
certificate verifier. Assertions are required; `-O` and `-OO` are rejected.

`reachable_guards.py` contains the original generator's source parser, finite
guarded control graph, and product worklist. The parser is ported from
`code/rebuild_machines.py` in the inherited context246 artifact. Its program
counter increment omits cleared trailing zeros; decoding pads with zeros and
checks that no nonzero suffix is discarded. The independent verifier keeps
the cleared zeros explicitly. All 8,391 decoded guarded edges were compared
after the port and agree.

## Output locations and reproduction

Run the following from the parent package directory, choosing fresh output
directories. `--output-dir` is mandatory for generation. The scripts preflight
their output filenames and use exclusive file creation, so existing outputs
and the supplied certificates cannot be silently overwritten.

```sh
python3 -B generators/reachable_guards.py --output-dir /tmp/zfc-product-recomputed
python3 -B generators/disjunctive_guards.py --output-dir /tmp/zfc-relational-recomputed
python3 -B generators/refine_guards.py --output-dir /tmp/zfc-refined-recomputed
```

The product generator writes `product-invariant.json` and the fuller
`reachable-guards.json`. Its generic initial mask is
`[7,1,1,7,7,1,7,7,7]` in logical order `N,T,W,A,D,H,X,Y,L`: `T=W=H=0`,
and the other six registers are arbitrary. It additionally computes the
restricted product root family `N,D>=2`, all other registers zero.

The disjunctive generator defaults to three value classes `{0}`, `{1}`,
`{2,3,...}` and writes `disjunctive-guards-3.json` plus
`disjunctive-invariant-3.zlib`. It starts from the single abstract vector
`[2,0,0,0,2,0,0,0,0]`. This means `N,D>=2` and all other registers zero;
it contains the actual `N=D=3` root, but does not cover the product generator's
whole generic root family. `--arity 2 3` also runs the earlier two-class
diagnostic. The fixed point and certificate format are unchanged from the
original exploration implementation; the portable changes concern paths,
CLI controls, output protection, and precise scope metadata.

The refined product generator defaults to exact-value cutoffs
`2,3,4,8,16,32,64`. At cutoff `k`, it distinguishes every value from 0 through
`k` and has a final class for values at least `k+1`. The initial condition is
the same generic six-numerical root family. `--cutoffs 2 3` selects a subset.
It checks its product invariant in memory and writes only
`refined-guards-summary.json`, as in the original exploration. These larger
product certificates were not retained for independent checking.

## Verified scope of the port

Each script accepts `--parse-only`, without requiring an output directory:

```sh
python3 -B generators/reachable_guards.py --parse-only
python3 -B generators/disjunctive_guards.py --parse-only
python3 -B generators/refine_guards.py --parse-only
```

These three entry points passed. The graph has 6,459 internal decoder nodes,
6,460 instruction sites, and 8,391 guarded cases. The portable generator's
source sites and all guarded successors were also compared with the
independent verifier. The report is `../results/generator-port-smoke.json`.
The full worklists were executed in the original investigation, and their
results are supplied in the package; the full worklists were not rerun after
this port. Execution times in the result files are observations from those
original runs, not prescribed limits.

The full-vector worklist computes the least reachable set in its finite
abstract graph. Independent certificate verification establishes that the
supplied set contains the initial vector and is closed under every abstract
successor. It does not independently check leastness. Neither statement
asserts that every admitted abstract vector has a concretely reachable
numerical representative.
