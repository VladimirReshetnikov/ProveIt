# Bounded physical searches and independent invariant closure

These files support two precise claims in the paper:

1. The primary K215 radius-five window invariant has **87,795 configurations** and passes **175,526 nonhalting successor obligations** in an independent closure audit.
2. On the final GC215 table, the supplied two-sided join search attempted **19,835,232 branch replacements** with a **48-step cap** and found **no additional state fold**.

They also preserve three smaller final-GC215 negative searches. None of these results proves that 214 states are impossible.

## Inputs and finite scope

`inputs.json` pins every table and the compressed and uncompressed invariant bytes. The primary table is already supplied among the packet's raw comparison representatives; the final GC215 table is in `machine/`. There are no external repository or workspace dependencies.

Each invariant starts at control 0 with **every** possible 11-bit local window. When moving the window, the abstraction includes both possible values of the entering exterior bit. Consequently inductive closure covers every binary initial tape from control 0, with an arbitrary head position. It does not assert reachability of every abstract window, nor coverage from an arbitrary initial control.

The primary invariant has 31 listed pairs distinguished by a neighboring bit. The final invariant has **88,375 configurations**, 31 such pairs, and no absent state/read-symbol row. Compressed inputs are preserved exactly; the closure auditor uses a list-of-bits successor calculation separately from the generator's bit-mask worklist calculation.

`primary.invariant5.audit.json` is the original independent audit receipt. `gc215.invariant5.audit.json` is the independently replayed closure receipt for the final table. These are finite arithmetic checks, not proof-assistant kernel theorems.

## Prepare and independently audit the inputs

Run from the **packet root**, using Python 3 with assertions enabled. The commands below write only to the chosen work directory. Change `/tmp/gc215-physical` if desired.

```sh
python3 research/physical-search/prepare_inputs.py --out /tmp/gc215-physical
python3 research/physical-search/audit_invariant.py reference/corpus/9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2.tm /tmp/gc215-physical/primary.invariant5.json --output /tmp/gc215-physical/primary.audit.json
python3 research/physical-search/audit_invariant.py machine/gc215.native.tm /tmp/gc215-physical/gc215.invariant5.json --output /tmp/gc215-physical/gc215.audit.json
```

To regenerate an invariant rather than just audit its saved closure:

```sh
python3 research/physical-search/local_invariants.py machine/gc215.native.tm --radius 5 --out /tmp/gc215-physical/gc215.regenerated.json
```

The source and exact compressed input hashes are in `inputs.json`; `prepare_inputs.py` also binds the C++ input bytes to those used for the delivered final search.

## Reproduce the reported two-sided search

A C++17 compiler is needed for this optional research replay. It is not needed by the packet's main verifier.

```sh
c++ -O3 -std=c++17 research/physical-search/two_sided_fold.cpp -o /tmp/gc215-physical/two_sided_fold
/tmp/gc215-physical/two_sided_fold /tmp/gc215-physical/gc215.invariant5.txt 48 > /tmp/gc215-physical/gc215.two-sided-fold.log
```

The delivered `gc215.two-sided-fold.log` contains the original result:

```text
radius 5; cap 48; attempts 19835232; one 167; both 0
```

Elapsed time is incidental. The search enumerates pairs with the smaller native label retained, and synthesizes each of the two survivor rows separately. A replacement row may use either write bit and either direction and target any surviving working state. The new path must join a positive old path within the 48-step caps, with exactly the same local tape and head and the identified control. It may not read outside the radius-five window or re-enter the retained state before a join. The second branch is attempted only when a candidate exists for the first branch. Thus `attempts` counts evaluated branch replacements, not complete two-row tables; `one` counts pairs surviving the first-branch filter and `both` counts complete candidate folds. The program's bounds, helper restrictions, and fixed native halt convention are part of the reported search family.

A found local candidate would still need an independent exact construction and whole-run simulation proof. This packet makes no claim based on a hypothetical unreviewed hit.

## Other final-GC215 negative searches

```sh
python3 research/physical-search/conditional_fold.py machine/gc215.native.tm /tmp/gc215-physical/gc215.invariant5.json --out /tmp/gc215-physical/gc215.conditional-folds.json --cap 48
python3 research/physical-search/double_marker.py machine/gc215.native.tm /tmp/gc215-physical/gc215.invariant5.json --out /tmp/gc215-physical/gc215.double-marker.json --cap 48
python3 research/physical-search/double_marker_join.py machine/gc215.native.tm /tmp/gc215-physical/gc215.invariant5.json --out /tmp/gc215-physical/gc215.double-join.json --cap 48
```

| Saved receipt | Search family | Evaluated candidates | Hits |
|---|---|---:|---:|
| `gc215.conditional-folds.json` | Keep one common row; synthesize the other to simulate one old step | 424,840 | 0 |
| `gc215.double-marker.json` | Two opposite-branch folds sharing a selector | 24,687 providers | 0 |
| `gc215.double-join.json` | Shared selector permitting positive joins of both executions | 24,687 providers | 0 |

The two shared-selector searches consider only disjoint recorded marker pairs with the same marker side and opposite differing read symbols. Helper providers exclude the four folded roles. The positive-join variant was made portable by deleting its earlier workspace-specific Python import path; its search algorithm is unchanged.

The source files contain the remaining exact restrictions. These bounded unsuccessful searches concern small local rewrites of the delivered machine. They neither rule out other source programs, other physical layouts, more general simulations, nor the separately proved new 216-to-215 decoder fold used to construct GC215 itself.

## Scanner records

The `scanner/` subdirectory preserves the inherited shortened-scanner failure
census and its one concrete counterexample, together with the new 205/204-DAG
source layouts and exact rotation recipes. Its README distinguishes unproved
contracts from semantic counterexamples and gives portable replay commands.
