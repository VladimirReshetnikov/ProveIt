# Edge-specific deletion of old107 in public253

The bounded search found no accepted 252-state table. It tested 502 new
nonuniform incoming-edge recipes and two uniform controls on the actual
public253 machine. Every candidate failed an affected affine runtime case;
no candidate qualified for a modified blank bootstrap run. Fuel and symbolic
abstraction failures remain unresolved, so this is no minimality result.

The input is mira-emmy's public PR20 reduction at
`0d544f2a2e3c18f12278441a74b7879f31cbe856`, derived from Mira-Cult's machine
and Jeff's verification using Andrew James Wade's framework. The literal
public table is copied to fresh scratch space and mapped to its old proof
labels. Its identity is checked against the four published edits to original254.
The full original frontend and theory are retained; these candidates change
two incoming targets and remove one binary state, without deleting logical rows.

Old107 has exactly two incoming edges:

```text
92/read0  = 0 L 107
130/read0 = 0 R 107
107/read0 = 0 R 121
107/read1 = 1 R 125
```

Both old104/read0 and old129/read0 equal old107/read0. The baseline affine
observer sees only a zero after the left-moving92/read0 edge, in 1,044 cases.
The right-moving130/read0 edge admits both next bits, in 15 and four cases
respectively; one case can encounter an edge more than once. Under the local
guard that the cell left of old92 is zero, redirecting92/read0 to104 or129
therefore gives the same complete configuration after two steps, ending in
old121 at the original head position. The finite observer does not prove
that guard on every reachable configuration.

For each s in {104,129} and each remaining working label q, the candidate
deletes107 and sets

```text
92/read0  := 0 L s
130/read0 := 0 R q.
```

There are 504 recipes. The two with q=s are uniform direct folds already
covered by the source04 family; the remaining 502 use different targets for
the two incoming edges. Source04's `context_search.py` redirects every
incoming edge to one state. Source25's `lab/fuse_states.py` additionally selects
each retained row from either source state, but still uses one global incoming
target. The nonuniform recipes here are outside both families. They also
differ from the all-start classification of the unchanged runtime252 body.

Every candidate has 252 working labels, 504 total binary rows, old start5 and
separate halt254. All targets remain within those working labels or the halt
label. All 55 conservative register-box pairs remain unchanged. No bootstrap
row of old5 is removed or repurposed.

The baseline passes all 8,391 affine cases at gap at least40 and independently
reaches the exact public bootstrap frame in 312,975 literal binary steps.
The new driver uses source04's attributed `program_sites`, `cases` and
`executor`, imported from scratch copies, with the unchanged published box
summaries. It records the 1,063 baseline cases affected by either patched edge
or old107, and screens those in deterministic order at fuel1,000. Any survivor
would receive all8,391 cases again, followed by a literal blank run with a
400,000-step limit. That run requires old96, head−17 and equality of the entire
tape, including all158 spare blocks and the blank exterior; it permits a
different arrival time. No candidate reached these later checks.

| First rejection | Recipes |
| --- | ---: |
| Affine fuel exhausted | 498 |
| Symbolic abstraction limit | 4 |
| Unexpected halt in a nonhalting case | 2 |
| Accepted by all affine cases | 0 |

Both unexpected halts occur at q=77 in case50, the `CC 2` site with path110111.
The abstraction failures occur at q=84 or120. Both uniform controls exhaust
fuel at case49, an increment site, after356 screened cases. Across the504
recipes, 2,660 candidate case checks were executed. No conclusion about an
arbitrary candidate's blank-tape halting follows from these failures.

The final default replay completed in 4.16seconds. It matches the earlier
development run's complete census; the final run adds explicit machine-count
metadata. The driver rejects optimized Python because its checks use
assertions. Run from any directory:

```sh
uv run --no-project python /path/to/Proofs/Computability/BusyBeaver/Research/ZFC/public253_context_search.py \
  --output /tmp/public253-context-results.json
```

`results/public253-context-results.json` records every recipe and first failing
case, all source/table identities, bounds, target frame and baseline checks.
No checksum manifest, network fetch, Coq or Lean build is used. The Python
affine summaries and candidate search are diagnostic code, not kernel proofs.
An independent read of the driver found the recipe family, protected rows,
full-survivor recheck, exact boot frame and result scope correct; it did not
perform another run or supply a kernel proof.

The strongest small formal interface suggested by this experiment is a
guarded92/read0 two-step rewrite, followed by a theorem transporting halting
through reachable-context block rewrites with positive progress and whole-tape
agreement. The guard must come from actual dispatch/PC/return invariants.
The existing `StateReduction` theorem instead requires one global state map;
it does not certify these nonuniform targets. This negative search supplies
no new consistency calibration, compiler simulation or internal ZFC endpoint.
