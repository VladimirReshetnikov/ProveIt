# Additional searches from PA194 and PA194C

These experiments found no certified 193-state construction. Their negative
results apply only to the explicitly bounded transformation/checker families
below. They are not lower bounds on PA-consistency machines, and a failure of
the symbolic checker is not a proof that a proposed machine is incorrect.

## 1. Existing-state local detours

`action_merge_all.cpp` extends the supplied PA194 action-merge search to allow
arithmetic-box controls as removed/retained states. Only the initial control
74 is excluded. Its abstract reachability starts with every tape window at
74, not merely the observed blank run. Each boundary shift nondeterministically
supplies either new boundary bit, so the resulting windows overapproximate
all tapes starting in control 74.

For each control/read pair it tries all 776 possible first actions having an
existing working control as target. Following that action, the original table
must reproduce the original single-step endpoint, including the entire window,
without leaving the window. Paired actions must avoid intermediate uses of
either edited control. This is a sufficient local merge certificate.

Both the PA194 and PA194C tables were searched with the following settings:

| Window radius | Maximum local duration | Contexts | Successful merges |
|---:|---:|---|---:|
| 4 | 120 | Abstract arbitrary-tape reachability | 0 |
| 6 | 160 | Abstract arbitrary-tape reachability | 0 |
| 8 | 200 | Abstract arbitrary-tape reachability | 0 |
| 4 | 120 | Source symbolic observations plus exact blank startup | 0 |

A final radius-eight, 200-step abstract-context run also found no local
merge or incoming-edge elimination for the supplied PA194 A/D-register
companion. Its literal native table is retained as `pa194AD.native.tm`.

The source-specific search uses 8,338 observed windows for PA194 and 8,240 for
PA194C across 171 non-box controls; other controls retain the abstract windows.
This restriction is a candidate-discovery aid. No positive candidate depended
on its completeness. A successful candidate would still require the complete
universal source check and exact startup.

## 2. Elimination by rewriting incoming rows

`incoming_eliminate.cpp` implements a different sufficient reduction. For a
noninitial state `a` without a self-loop, it rewrites every transition targeting
`a`, seeking an action that simulates the old two-step block through `a`.
The replacement must rejoin the exact old endpoint on every supplied window,
avoid `a`, and avoid all edited incoming rows until that endpoint. The latter
condition makes simultaneous replacement of the incoming rows sound. If all
incoming rows have a replacement, `a` can be deleted without a state alias.

There are 172 eligible states in each table. The same four radius/context
settings above found no complete deletion certificate in either PA194 or
PA194C. This method is more general than simply redirecting an incoming edge
to an unchanged state, but still explores only a small specified rewrite family.

## 3. Full source-contract state quotients

`merge_contracts.py` checks a nonlocal rule. It merges every pair of the 170
controls outside the 23-state arithmetic box and the dispatcher 84.
The retained zero and one actions are chosen independently from either old
state, and all incoming targets are renamed. Thus there are
`4 * binomial(170,2) = 57,460` candidate tables per family, including some
duplicate row choices.

Unlike the local searches, a candidate may travel outside a bounded window:
it must rejoin at the complete symbolic source-instruction frame. The checker
has a bound of 1,024 symbolic steps for each contract. Every affected contract
is checked; unaffected contracts have unchanged traces. Promising candidates
would undergo a fresh full-contract validation, independent physical/list-lemma
replay, and exact blank startup before acceptance. Arithmetic-box controls are
not removed or given selected replacement actions, but target renaming can
change their outward edges to controls 4, 5, or 302; this is another reason that
a positive preliminary result would need independent physical verification. No candidate passed the affected-contract stage.

| Family | Candidate tables | Contract executions | Certified merges | Runtime |
|---|---:|---:|---:|---:|
| PA194 | 57,460 | 245,263 | 0 | 59.53 s |
| PA194C | 57,460 | 244,771 | 0 | 84.43 s |

The exact receipts are `merge_contracts_S.receipt.json` and
`merge_contracts_C.receipt.json`. These are checker-based exclusions of a
finite search family, not proofs that every candidate is semantically invalid.

## 4. Expanded quotient actions

`action_options.cpp` records every separately valid first-action detour from
the radius-four source-context experiment. `expanded_contracts.py` uses the
union of these choices for either state when forming a pair quotient, then
checks full source contracts as above. It excludes combinations already tested
in the direct row-selection family. Complete expanded results were:

| Family | Additional candidate tables | Contract executions | Certified merges | Runtime |
|---|---:|---:|---:|---:|
| PA194 | 171,009 | 541,573 | 0 | 186.92 s |
| PA194C | 174,457 | 548,997 | 0 | 160.11 s |

Exact results are in `expanded_contracts_S.receipt.json` and
`expanded_contracts_C.receipt.json`. Combining direct and expanded searches
across both families gives **460,386 candidate tables** and **1,580,604
symbolic contract executions**, with no positive preliminary result. These
are counts of tried row-choice constructions, not of pairwise nonisomorphic
machines.

## 5. Scanner and register-allocation checks

The PA194 source has 25 instruction paths containing a run of six zero bits.
Deleting the final zero-scan control 34 by changing `(23,0)` to `0 L 75`
fails the full symbolic source check at the first source instruction. Therefore
the tempting reduction `134 fixed -> 133 fixed` cannot be justified by merely
shortening the old scanner. Both the controller and the emitter path bounds
would have to be redesigned and rechecked.

A coarse zero/nonzero register analysis from source site 25 with logical
register mask `N > 0`, all other registers zero, reaches 263,888 abstract
configurations across 3,671 source sites. It certifies no pair of the nine
logical registers as safely coalescible. The abstraction is deliberately
coarse: a positive decrement may leave either zero or a positive result.
This is only a failed sufficient register-allocation test.

## Reproduction and provenance

Compile the C++ programs with a C++17 compiler. A typical complete local run is:

```
g++ -O3 -std=c++17 action_merge_all.cpp -o action_merge_all
./action_merge_all pa194.native.tm 8 200
g++ -O3 -std=c++17 incoming_eliminate.cpp -o incoming_eliminate
./incoming_eliminate pa194.native.tm 8 200
python3 merge_contracts.py --family S
```

The packaged scripts resolve the cached-controller construction automatically
at `../../construction/`, relative to this directory, so run
`python3 merge_contracts.py --family C` without an external checkout. An optional
`PA194C_CONSTRUCTION` environment variable overrides that path. The same rule
is used by `contexts194C.py` and `expanded_contracts.py`.

All command examples assume this `search/local/` directory as the current
working directory. The PA194C input for the C++ searches is `pa194C.native.tm`.
Python inputs and sibling construction dependencies are located relative to
the script paths, so the Python commands can also be invoked from elsewhere.

The native PA194 table is copied from the supplied PA194 packet. Its SHA-256 is
`e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54`.
The source resolver and `symbolic_runtime.py` are reconstructed from the
unchanged supplied compiler/checker, with the exact PA196 `Program.lean`
retrieved at ProveIt commit `b88235336c63a247852fe8ec7f931d51f953632d`.
The emitter tree in `reconstructed_tree.json` was recovered from the literal
PA194 reader transitions. It has 67 distinct reader subtrees and expands to
190 tokens, 3,673 primitive sites, and 4,780 outcomes. It reproduces exactly
the supplied PA194 verifier totals: maximum 497 and total 1,479,348 symbolic
steps. These scripts inherit the original authors' source and licenses; they
do not constitute an independent arithmetic-box proof or a Lean endpoint.

For future work, the most promising remaining directions are changing the
source controller to shorten the required zero-scan bound, proving stronger
register liveness invariants, or allowing more substantial tape encodings
in the quotient relation than identical source-frame tapes.
