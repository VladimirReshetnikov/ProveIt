# Lean semantic coverage and decoder-suffix proposal

This is a compiled component proposal for the exact K215 proof, pinned to ProveIt
commit `6f0d42d368506bc29c70ace1c992ed88b2651346`. It does not alter the Turing
machine, source program, calculus, old checker definitions, or public simulator
theorem contracts. It exposes the concrete semantic facts consumed by the
simulation induction, so that shared decoder proofs and shorter primitive
suffix checks can replace repeated whole-site execution.

## Contents and result

* `src/BusyBeaver/ZFC/KSim.lean` is the replacement simulator. `EdgeSpec` records
  the exact branch contract; `SemanticCovered` retains each exact decoded leaf
  and consumed path. `Semantic.halts_iff` uses those contracts. The original
  `KSim.halts_iff`, `sim_step`, `sim_stop`, `sim_halt`, `runTo_sound` and
  `runHalt_sound` signatures remain available.
* `KSimPrefix.lean` composes any uniform exact decoder prefix with a positive
  primitive suffix, proves the suffix executor sound, and converts finite-tree
  leaf contracts into semantic coverage.
* `KDecoderSuffix215.lean` connects that interface to the maintained, exact
  `KDecoderPrefix215.leaf_prefix` theorem. Its complete-source conclusion is
  explicitly conditional on `CheckedLeafSuffixes` and source-shape totality.
  **Those global premises are not discharged by this packet.**
* `KDecoderSuffix215Example.lean` proves one literal source leaf, word `000`
  with instruction `decnz 8`. It retains both consumed prefix bits at the exact
  state-27 entry port, checks both zero and nonzero decrement suffixes with
  `decide +kernel`, and closes `semantic_site` using the actual table's register
  engine theorem. This accounts for **two of the 6,176 branch outcomes**;
  no complete suffix-coverage result is claimed.
* `KSimCompatibility.lean` contains seven typed clients: six original public
  APIs and the new semantic halting-equivalence API.
* The other 24 Lean files are unchanged dependency snapshots from the pinned
  repository. Their original attribution headers are retained.
* `KSim.patch` changes only the maintained simulator; `baseline/KSim.lean`
  contains its exact predecessor; `source-pins.json` binds all 29 delivered
  module sources and their upstream origins by SHA-256.
* `evidence/` contains the accepted fresh build receipt and raw compiler logs.
  Compiled objects are deliberately absent from the deliverable.

## Mathematical contract

For a consumed word `Q`, branch `br`, and exact target symbolic configuration
`t`, `RunToSpec M br Q t` asserts

```lean
forall (n : Nat) {vs : List Nat}, Valid br vs ->
  Reach1 M (conc n vs (start Q)) (conc n vs t)
```

The quantifier includes gap zero and every valid register valuation. `Reach1`
requires at least one physical transition. It is preserved when composing an
arbitrary `Reach` decoder prefix with a positive suffix. This is the strict
decrease used by backward halting transfer; a zero-length prefix is permitted.

`EdgeSpec` keeps the original path bound `Q.length <= 48`, register bound
`r < 9`, both decrement branches, their exact `Valid` hypotheses, and the
original `tgtConf` including overflow, growth, and spare-register behavior.
Malformed `.node` leaves have specification `False`.

The halt branch uses `HaltPortSpec`: every valid concretization reaches a
configuration whose state is 230. This needs no terminal-row assumption.
`Semantic.halts_iff` retains the original separate hypothesis that both rows
at state 230 are terminal. Thus even `sim_step` keeps its original API, without
acquiring an unnecessary terminal-row premise.

## Verification boundary

The self-contained build uses Lean 4.32.0 and only its standard library. All 29
project modules are freshly compiled in dependency order. No Lake download,
mathlib, precompiled project object, `sorry`, `admit`, `native_decide`, or new
axiom declaration is used. The final receipt binds exact source and log hashes.

The new generic `Semantic.sim_step` and `Semantic.halts_iff` report only
`propext` and `Quot.sound`. The existing-checker adapter and original public
halting theorem report the original standard three: `propext`,
`Classical.choice`, and `Quot.sound`. The literal suffix computation reports
`propext` and `Quot.sound`; its closed semantic theorem reports the standard
three. These reports concern the named component theorems, not a fresh build
of the complete ZFC endpoint.

The full 192-module K215 endpoint closure and the nine site batches are not
rebuilt here. The proposal preserves their old interface, but integration must
rebuild affected descendants before it becomes a maintained endpoint receipt.

## Reproduce

Run with the exact Lean 4.32.0 executable:

```bash
python3 build.py --lean /path/to/lean --out /path/to/fresh-build
```

The script builds serially under the shared build lock, always recompiles every
module, and writes its logs and `receipt.json` outside `src/`. It rejects a
different Lean version, nonzero compiler exit, and unexpected named audit
axioms. It requires no network access. The compiler and standard library must
be installed beforehand. The recorded elapsed times describe this component
check only; they are not an end-to-end speedup benchmark.

## Integrate and continue

From the pinned ProveIt checkout, apply `KSim.patch`; add the three new
`KSimPrefix`, `KDecoderSuffix215`, and `KDecoderSuffix215Example` modules under
`Computability/BusyBeaver/Lean/BusyBeaver/ZFC/`. Keep the compatibility module as
an audit client. Do not copy unchanged dependency snapshots over a newer
checkout; reconcile against `source-pins.json` instead.

The original simulator has 356 lines / 16,146 bytes. Its semantic-interface
replacement has 460 lines / 20,505 bytes, an increase of 104 lines / 4,359 bytes.
This packet claims no immediate source-size or endpoint-build-time reduction
from that refactor. It supplies the missing proof interface needed to replace
thousands of repeated decoder executions without changing the simulator's
statement or weakening its obligations.

The next bounded step is to generate and check suffix certificates for all
literal source leaves, using each exact uniform port. All 6,176 branch outcomes
must remain covered. Once the all-leaf premise and source totality are proved,
the already-compiled conditional theorem supplies semantic source coverage.
Subsequent work may replace repeated suffixes with parametric primitive
contracts; that additional proof sharing is not completed here.

## Attribution

`LICENSE.upstream` is the repository's license. `NOTICE.K215.upstream.md`
retains machine and calculus attribution. Existing module headers identify
ports and adaptations of Elliot Glazer's k230-rocq and Jeff Ketchersid's m254
verification, among other repository contributions. Some unchanged historical
comments describe their former draft status; the accepted receipt here records
the exact versions freshly compiled for this component experiment.
