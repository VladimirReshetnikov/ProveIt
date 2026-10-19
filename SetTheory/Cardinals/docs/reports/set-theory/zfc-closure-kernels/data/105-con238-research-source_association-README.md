# Source associativity with arbitrary middle control

This supplement proves and implements a broader source reassociation rule,
and supplies an exactly equivalent source with shorter instruction paths.
It is independent of the accepted 238-state machine. No additional machine
state reduction is claimed here.

## The source lemma

For nonempty source trees A, B, C, the transformation

```
A ; (B ; C)  <->  (A ; B) ; C
```

preserves the complete ordered instruction/control graph in every surrounding
context provided A has no escaping break and C has no escaping continue.
B may have arbitrary control exits; halt leaves are allowed. The proof and
the exact meaning of escaping exits are in `boundary_associativity.tex`.
The two conditions are necessary and sufficient for equality of the complete
local signatures with distinct symbolic external targets. This necessity is
about the full control graph, not semantic equivalence after restricting to
reachable instructions or a particular outer context.

Two boundary counters per source node decide the criterion. Independent
literal-path calculations check all 328 possible single rotations of the
exact inherited boundary source: 245 are admitted, including 20 excluded by
the previous all-chunks-closed rule. The certificate includes six concrete
rejected witnesses and four small illustrative examples.

## Concrete result

| Source property | Inherited boundary source | New equivalent source |
| --- | ---: | ---: |
| Ordered instruction leaves | 6,455 | 6,455 |
| Guarded control edges, including halt | 8,386 | 8,386 |
| Distinct source subtrees | 224 | 224 |
| Longest instruction path | 48 | **39** |
| Longest consecutive-zero run | 6 | 6 |

The replay has 19 source transformations, five using the broader rule.
An independent checker rebuilds the complete control graph after each step
and compares every operation and every possible branch with the inherited
source. This proves source equivalence for arbitrary natural register values;
it is not a finite test on selected register assignments.

The bounded beam used width 150 and 20 levels, capped the source DAG at 224
nodes and the zero run at six, and examined 625,858 generated alternatives.
Of these, 40,486 used a rotation outside the previous all-closed rule.
These are generation counts; alternatives may recur across levels.
The search did not find a source with 223 nodes under those settings.
This is a bounded result, not a lower bound.

Source graph size does not determine binary TM state count. Reassociation
can alter backward decoder projections, contextual state sharing, and startup
behavior. The shorter-path source is supplied for future compiler co-design;
it has no accompanying binary correctness claim.

## Reproduce the exact checks

Python 3 standard library only, with assertions enabled. From this directory:

```sh
python check_associativity.py
python check_source_result.py
```

The optional search takes roughly four minutes in the original environment:

```sh
python exact_reassociate.py 150 20 224
python check_source_result.py
```

The search writes `best_source.json` and `search_stats.json`. A separately
checked result is already included. The entire source is in the `sites`
field of `best_source.json`; `structures` and `history` give a compact,
exactly replayable derivation from the inherited root.

## Inputs and attribution

`boundary_sites_input.json` is copied byte-for-byte from the prior
`ZFC_239_State_Construction_2026-10-19` archive's
`candidate239/sites_logical.json`, SHA-256
`7fd152d1f5371d2a561d4ad1870d241683b010ce7b7a27399b95363a4537cfb6`.
`boundary_source_input.json` retains the exact `root` and `structures` fields
from that archive's `source_encoding/boundary_success.json`.
The original calculus and program are credited to Mira-Cult, upstream machine
verification to Jeff Ketchersid, and the compiler framework to Andrew James
Wade. The boundary-source reparenthesization and the preceding source
reductions retain their existing ProveIt and incoming-report attribution.

The broader criterion and the new source search are supplementary work for
this session. No exhaustive literature-priority claim is made. No new license
is asserted over inherited source data; retain the main package's original
notices and licenses with these inputs.

## Files worth retaining

- `boundary_associativity.tex`: report section with proof and concrete result.
- `exact_reassociate.py`: source search and independent local signatures.
- `check_associativity.py`, `associativity_certificate.json`: all single
  rotations of the inherited source and concrete rejected witnesses.
- `check_source_result.py`, `source_result_certificate.json`: exact history
  replay and all guarded control edges after every rewrite.
- `best_source.json`: complete new source and derivation.
- `boundary_source_input.json`, `boundary_sites_input.json`: exact inputs.
- `search_stats.json`, `exact_reassociate_fast.log`: bounded-search evidence.
