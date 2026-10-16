The public compiler route is usable despite the missing original `source.py`.
At upstream commit `297ab8df7e5de329605c3875b4934643b371a5e3`,
[`ZF/generator/`](https://github.com/jeff87654/busy-beaver/tree/297ab8df7e5de329605c3875b4934643b371a5e3/ZF/generator)
contains Andrew Wade's `TMBuilder.py`, `tm.py`, `tmdb.py` and `zf2.py`, with
`LICENSE.wade` granting MIT No Attribution terms. It also contains the
configurable `zfp.py`, formula tables and `mkcand.py` used for earlier
335–361-state machines. These are different from Mira-Cult's unavailable
254-state compiler and optimization bundle.

The published finite table in `ZF/m254/coq/prog/Dag254.v` retains the
219-node register program, its root, all node names and its nine-register
order. Reading this file as data suffices to reconstruct the program at
Wade's backend interface. `recover_wade_dag.py` performs that reconstruction,
executes the pinned backend only on an outside-repository scratch copy, and
independently inverts every emitted decision edge to check the original DAG.
It reproduces **281 working states: 219 decision states and 62 framework
states**, without the original Python source. The measured output and input
pins are recorded in `wade-route-evidence.json`.

The output has 561 rows and one implicit halting transition,
`1.inc` on symbol `1`. For the existing Lean `Machine` model, explicitly
filling a missing row with “write the read symbol, move right, halt” preserves
halting and final score, while adding one final head move. This normalization
and the register-program simulation still need Lean proofs. Re-extracting
the same DAG is executable evidence about the generated data, not a proof of
the whole interpreter or a ZFC endpoint. The final 254-state table itself is
represented separately in `Table254.lean`.

Reproduction from the ProveIt root, offline from the unchanged vendored
snapshot (an optional `--upstream-clone` checks a separate clone's pinned
objects):

```sh
uv run --no-project python Computability/BusyBeaver/Research/ZFC/recover_wade_dag.py \
  --scratch /tmp/zfc-wade-route \
  --output-evidence /tmp/wade-route-evidence.json
uv run --no-project python Computability/BusyBeaver/Research/ZFC/generate_table254.py --check
```

The next practical compiler experiment can replace the theory-emission DAG
while retaining a common proof calculus, enumerator, register order and
backend. A count below 254 on Wade's 62-state framework would require at most
191 decision states, compared with the recovered baseline's 219. That is a
measurable target; shortening a displayed formula alone does not establish it.
The framework cost itself depends on the emitted tree and must be measured
again for each candidate, as the 2-adic experiment below illustrates.
The published `Prog254.v` also retains the larger decoder tree from the final
machine. Direct data extraction finds 6,459 reachable internal nodes and
6,460 instruction paths of maximum length 34: 2,601 increments, 1,931
decrements, 128 breaks, 1,799 continues and one halt. Thus the original
`paths.json` is absent, but equivalent instruction-path data is recoverable.
Recovering those paths does not recover the original decoder optimizer or a
compiler for Mira-Cult's smaller interpreter.

The final table does not have a justified decomposition into the published
219-node DAG plus 35 framework states. It has 178 states whose two actions
preserve the read bit and move right; only 44 of those can be reached from
dispatch state 96 without crossing a state of another shape. The resulting
frontier has 26 states combining decode routing with writes, left moves or
engine entries. The upstream design notes describe these contextual folds.
The next assembler task is to recover per-instruction phase contracts for
this shared engine, using the published symbolic sites as specifications,
and prove them in Lean. Cutting out a purported 35-state framework would
discard those contracts. The current Lean quotient theorem alone cannot
justify that transformation.

Naively replacing recursive Cantor pairs with 2-adic pairs makes this
particular unary-register backend larger. `pairing_backend_experiment.py`
replaces the pair root and both unpair roots in the recovered DAG and measures
the generated tables:

| Pair helper | Unpair helper | Decision states | Framework states | Total |
|---|---|---:|---:|---:|
| Cantor | Cantor | 219 | 62 | 281 |
| 2-adic | Cantor | 230 | 62 | 292 |
| Cantor | 2-adic | 231 | 63 | 294 |
| 2-adic | 2-adic | 242 | 63 | 305 |

The mixed rows isolate costs and have incompatible encoders and decoders.
The matched replacement passes 570 small helper-contract cases, but has no
whole-program calibration or Lean simulation proof. Its formula constructors
would encode `Rel(0,0)` as 5 rather than 1, and the experiment changes the
designated target accordingly. These are compiler measurements, not new
ZFC-inconsistency machines. `pairing-backend-results.json` records the exact
variants and test counts.

The helper invariant is explicit. Pairing requires a zero output register,
consumes the two inputs and produces `2^head * (2*tail + 1)`: first form the
odd part, then double once for every consumed head unit. Unpairing requires
two zero outputs. Input zero returns `(0,0)` immediately. For positive input,
each even stage divides the positive input by two and increments the head
count; the first odd stage returns its half as the tail. Consequently the
division loop terminates, and every positive code has strictly smaller tail.
Those facts support finite-list progress; the actual command encoding and
its proof-search completeness must still be connected to them.

The Diophantine-inspired stream experiment in `stream_encoding.py` instead
uses 2-adic cells for small flat token tags and variable fields. That avoids
exponentiating an already enormous subformula code and may support a simpler
direct tape interpreter. The negative unary-backend result above does not
settle that separate architecture. Reproduce it with:

```sh
uv run --no-project python Computability/BusyBeaver/Research/ZFC/pairing_backend_experiment.py \
  --scratch /tmp/zfc-wade-pairing \
  --output-evidence /tmp/pairing-backend-results.json
```

`StateReduction.lean` proves that exact transition quotients preserve finite
runs, arbitrary-tape and blank-tape halting, and final score in both directions
in the existing Busy Beaver model. It covers the auditor's step-bisimulation
rule. The auditor's stronger finite-window/macro rule remains supported by
its stated mathematical argument and executable checks; it has not been
formalized in Lean. The literal 254-state audit finds no reduction by either
rule, so there is no smaller-state claim from these experiments.
