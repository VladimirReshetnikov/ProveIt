# Direct negation, coupled routing, and grammar research

## Result and scope

This contribution supplies a **247-state control machine** with a shorter
negation constructor and a coordinated physical routing change. It does not
meet the requested fewer-than-245-state target. The control uses 130 grammar
roles and 117 retained framework roles. A successful candidate within this
framework would need at most 127 grammar roles.

The original AX emitter contains 30 copies of the nine-token constructor
`LNPQMVQPW`. At its clean arithmetic interface each can become `LMPW`, reducing
the exact AX fine word from 1,270 to 1,120 tokens. The theory contribution proves
the constructor identity and checks every occurrence in the complete symbolic
AX execution. This directory realizes the changed source using a modified
physical atom and supplies the full literal binary table. The runtime
contribution proves its 7,311 guarded cases over unbounded counter values.

These are three distinct results: a source identity at a specified interface,
a grammar/source reassociation certificate, and the all-values literal binary
runtime validation. Finite search outcomes in other subdirectories are not
additional machine proofs.

## Prior art and precise contribution

The source program and calculus originate with Mira-Cult; Jeff Ketchersid
provided the upstream formal verification, and Andrew James Wade supplied the
compiler framework. This work starts from the attributed ProveIt research
artifacts pinned at commit `fd1adfa19f8fe8da41444e3fa43b89a59d891067`.

The [ProveIt incoming index](https://github.com/VladimirReshetnikov/ProveIt/blob/fd1adfa19f8fe8da41444e3fa43b89a59d891067/docs/incoming/README.md)
already records pairing-shift negation in intakes 158/159, including the
source56 contribution and a 255-state available audit. That related idea uses
the arithmetic identity `P(x,1)=P(0,x)+2`. It is prior work on optimizing the
negation constructor. We therefore do not claim that negation optimization in
general is new. The concrete contribution here is direct retention of the
formula in scratch storage, the joint `LM` source/physical-route change, and the
complete occurrence audit plus literal runtime replay for this realization.

Previous fine-grammar searches already covered DNE and Boolean AX changes,
schema permutations, disjoint and affine commutations, and many routing
reassociations. The trace experiment here combines the existing DNE32 input
with a more general trace-ideal quotient mutation. It is a negative search
result, not a new lower bound.

## Constructor identity and interface

Write `T,S,U,V` for logical registers 1,2,6,7, and
`P(x,y)=(x+y)(x+y+1)/2+y`. The relevant fine blocks are read from the pinned
source AST:

| Fine word | Effect used in the proof |
|---|---|
| `L` | Move `T` into `U`, clearing `T` |
| `M` | Increment `T` |
| `N` | Move `S` into `T`, clearing `S` |
| `P` | Clear `T,U` and add `P(U,T)` to `V` |
| `Q` | Move `V` into `S`, clearing `V` |
| `V` | Inverse-pairing block on the stack |
| `W` | Add `4V` to `T`, clearing `V` |

With `U=V=0` initially, `LMPW` produces
`(T,S,U,V)=(4P(T_old,1),S_old,0,0)` and leaves all other registers unchanged.
The old constructor pushes the old top onto the stack, creates falsity, then
immediately pops the saved top to form the implication. It produces the same
result. The independent proof establishes the stronger sufficient condition
`V=0`, allowing arbitrary initial `U`; the output then contains
`4P(T_old+U_old,1)`. Arbitrary nonzero `V` does not satisfy the identity.

See `../theory/negation_peephole_proof.tex`,
`../theory/audit_negation_peephole.py`, and
`../theory/negation_audit.json`. The occurrence certificate for the five screened
AX variants is also retained in `direct_negation_variants.json` as exact old
and new words and zero-based old-word occurrence offsets. Token counts are
counts in the 30-symbol fine vocabulary, not Turing-machine state counts.

## Coupled source and physical routing

`prepare_lm_backend.py` derives all changes from the original AST and verifies
that node 112 has node 113 as its only parent:

| Item | Old definition | New definition |
|---|---|---|
| AST112 | `(57,42)` = `LNPQ` followed by `M` | `(40,42)` = `LM` |
| AST113 | `(112,78)` = old negation | `(112,77)` = `LMPW` |
| Source state 237 | `(218,105)` | `(218,124)` |
| Physical 218, read 0, projection 00 | `LNPQ` | `L` |
| Physical 218, read 0, projection 10 | `VQPW` | `VQPW` |

The other projection targets whose source definitions contain negation change
coherently: 183/1 at 11, 153/1 at 11, and 159/0 at 10. All 22 projection equations are
listed in `lm-backend/backend.json`. The modified vocabulary still has 44
physical terminal words and 127 distinct original sequence words, with no
terminal/sequence collision. Physical 218 has two entry variants: its new
variant 0 implements `LM`, and variant 1 retains `VQPWM`.

Lifting the original 128-rule grammar needs two extra routing carriers in the
frozen control. One accommodates the changed 00 projection of 218. The other
replaces an old use of the negation tree as a dummy routing carrier: the old
negation's 01 projection exposed `VQPW`, whereas the new negation exposes `PW`.
This explains the initial 130-role result. It is a cost of this realization,
not a proof that two extra roles are necessary in every possible realization.

`lm-control/grammar.json` is the frozen input for the validated table.
`lm-warm/search0.json` is a later, different grammar with the same 130-role
count. Do not substitute it when replaying the archived control witness.
`lm-control/input-freeze.json` records exact byte comparison of the frozen
seed replay with the original emitted tables, sites and certificates.

## Verification of the control

The control artifacts are in `lm-control/`:

* `machine.tm` has dense states 0 through 246 and halt state 247.
* `machine_old.tm` retains source labels and is the input to the literal
  runtime verifier.
* `grammar.json`, `allocation.json` and `renumbering.json` bind the grammar to
  the concrete table.
* `sites_logical.json` and `sites_physical.json` describe all 5,650 primitive
  source occurrences; maximum path depth is 52 and maximum zero run is 6.
* `register_bisimulation.json` proves reassociation of the **modified** source
  through 2,584 state pairs and 5,166 edges, with one halt pair.
* `blank_boot.json` records the exact 407,915-step blank bootstrap.
* `frozen-input-audit.json` binds the finite audit to the frozen grammar.

The stronger literal runtime proof is in
`../runtime/lm-control-validation/validation-summary.json` and
`../runtime/lm-control-validation/whole-frame.json`: 7,311 guarded cases,
2,010,611 symbolic rules, and at least 13 literal steps per checked macro.
The partition and affine checks cover unbounded counter values; these are not
merely 7,311 sampled register assignments. The graph audit finds all 247 states
reachable in the transition graph and 247 distinct exact transition-congruence
classes. This rules out an immediate unreachable-state or identical-row
quotient of this table; it is not a general machine minimality theorem.

The source identity is used at the clean AX interface. We do not assert that
the old and changed register programs are equivalent from every arbitrary
register assignment. Reassociation of the changed program is separately
checked for arbitrary register assignments. The overall logical calibration
to the original ZFC enumerator uses the interface theorem in the theory
contribution and the inherited original-source calibration. No new
proof-assistant theorem completing that entire chain is claimed here.

Control table SHA256:

```
machine_old.tm 53fc5a9c55102e756e32374a643a03b7983da336074e73253a80694886db1845
machine.tm     50c55ea80eaa10f537ff9eeab522124b851e844bbb79f8f839513a361d3906f7
```

## Recorded search outcomes

| Search | Input AX tokens | Initial grammar roles | Best roles | Proposal iterations |
|---|---:|---:|---:|---:|
| DNE32 with trace-ideal mutations |1,252|128|128|8,083,093|
| Coupled LM, original AX |1,120|130|130|5,561,251|
| Coupled LM plus DNE32 |1,112|131|130|2,802,443|
| Coupled LM plus eight-DNE Church layout, patched search |1,056|135|134|1,611,191|
| AX-only contraction, original source interface |1,120|142|139|308,387|
| AX-only contraction, DNE32 |1,112|140|139|351,122|
| AX-only contraction, Boolean24 |1,112|148|140|590,216|
| AX-only contraction, DNE63 |1,072|142|139|554,881|
| AX-only contraction, eight-DNE Church layout |1,056|151|140|390,130|

Each main final grammar has its independent finite audit. The five AX-only
audits use the inherited fine-grammar checker. The trace audit rederives all
30 fine blocks and their actual read/write supports from the source AST,
constructs a full dependence DAG independently of the C++ implementation,
checks 22 routes and 54 bootstrap equations, and realizes the final trace word
literally. Its retained best witness changes no source-interface word.

`joint_router_search.py` additionally tries simultaneous reparsing of a
carrier root and both children, with up to one or two new constrained child
words in the finite current dictionary. The two recorded screens examine 11
and 14 assignments, respectively, and retain 130 roles. These tiny constrained
domains are not exhaustive over new words or coupled changes of several
different carriers.

The final Church-layout combination has 14 remaining negations after its
eight DNE cancellations and a different schema/bundle order from the original
AX. Its first coupled-LM run started with 138 roles and reported 134 after
2,379,638 proposals, but the independent audit rejected that saved witness.
`lm-church8-warm/rejection-audit.json` labels it `INVALID_ROUTING_TRACE`.
The exact defect was a route through the word `LNPQXJLNPQSU`, which is a
physical terminal. A synthesis proposal temporarily gave that terminal a
transparent dictionary rule, making route 243/read1/prefix01 appear valid.
Garbage collection removed the temporary rule and left a broken projection.
The inherited engine checked full paths before collection and checked only
route roots afterward.

`anneal_fine_routing_closed.cpp` prevents descent through physical terminals
and checks every projection again after collection. The inherited vendor
file remains unchanged; `routing-closure.patch` records the fix.
`audit_router_collection.py` reconstructs the retained failure and checks both
rejection mechanisms. Repairing its route produces an independently valid
135-role seed. The patched 90-second run reaches a different, independently
valid 134-role grammar after 1,611,191 proposals, with zero closure rejections.
It is retained in `lm-church8-repaired/`; it has not been emitted or
runtime-certified as a new literal machine. The earlier independently checked
128-role trace and 130-role LM witnesses remain valid.

The raw source-DAG seed in `lm-backend/seed.json` has a zero-run bound 7 and was
not a valid zero6 start. Its 360-second exploratory run accepted no move; it is
retained as a diagnosed initialization failure and is excluded from the
successful-search totals. An early DNE launch with missing inputs was aborted.
Neither failed configuration supplies a negative result about valid grammars.

## Reproduction

From the archive root, run:

```sh
python work/grammar/reproduce.py \
  --fine dependencies/fine_grammar \
  --output replay/grammar
```

This command independently audits the retained main grammars, re-emits the
frozen 247-state control, replays its exact source reassociation and blank
bootstrap, and compares eight exact output files with the archived control.
The `--fine` argument is required so historical absolute provenance paths are
not silently used. Run the runtime contribution's separate reproduction
driver for the complete all-values binary-frame proof.

To rerun the timed stochastic searches as well, add `--search`; a C++17
compiler is required. Current LM reruns use the fixed route checker; historical
engine commands remain recorded in each run's command JSON. Search budgets are
wall-clock limits, so proposal counts
and best serialized grammars need not reproduce byte-for-byte on a different
machine. The archived certificate replay is deterministic.

To regenerate the new LM source inputs and the original warm seed:

```sh
python work/grammar/prepare_lm_backend.py \
  --fine dependencies/fine_grammar --output replay/lm-backend
python work/grammar/lift_lm_seed.py \
  --backend replay/lm-backend \
  --seed work/grammar/inherited_inputs/original128.json \
  --output replay/lm-warm
```

The corresponding DNE composition is:

```sh
python work/grammar/prepare_lm_dne_backend.py \
  --backend replay/lm-backend \
  --inherited work/grammar/inherited_inputs/dne32_128.json \
  --output replay/lm-dne32-backend
python work/grammar/lift_lm_seed.py \
  --backend replay/lm-dne32-backend \
  --seed work/grammar/inherited_inputs/dne32_128.json \
  --output replay/lm-dne32-warm
```

The final Church-layout inputs are reproducible from the retained AX-only
screen and its explicitly rejected routing proposal:

```sh
python work/grammar/prepare_lm_dne_backend.py \
  --backend replay/lm-backend \
  --inherited work/grammar/direct-neg-seeds/mask2004/screen.json \
  --output replay/lm-church8-backend
python work/grammar/lift_lm_seed.py \
  --backend replay/lm-church8-backend \
  --seed work/grammar/lm-church8-warm/search0.json \
  --output replay/lm-church8-repaired
```

Here the rejected proposal is only a pool of exact word productions. The
lifting step independently reconstructs all route obligations, adds the
missing carrier, and yields the validated 135-role seed. The invalid route is
not inherited as a premise.

`inherited_inputs/provenance.json` records the input hashes and original
locations. `vendor/NOTICE.txt` retains the inherited attribution. Newly written
scripts in this directory derive their exact arithmetic and source meanings
from the pinned source; finite words are never used as a substitute for their
required logical interface proof.
