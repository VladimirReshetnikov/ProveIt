# Checked guarded frames for K215 control routines

This is a small, independently replayed proof component for the literal maintained
215-state table. It completes the missing generic frame rule and all 35 universal
template contracts from the existing `round13-left-frame` proposal. It does not
replace production coverage and does not rebuild the full ZFC endpoint.

## New checked results

* `KLeftFrame.sstep_natural`: every guarded symbolic step commutes with appending
  an arbitrary left frame, including the failure case.
* `KLeftFrame.unsafe_frame_counterexample`: the empty-left guard is necessary.
* `KLeftFrame.runLocal_sound`: one finite local certificate lifts to every frame,
  every gap parameter and every valid register file.
* `KLeftFrame.local_home`: composition with the existing Home proof gives a
  positive whole-tape run for every caller prefix accepted by `scanBound`.
* `KLeftFrame215.all_checked`: ordinary kernel reduction checks all 35 actual-table
  local bodies, containing 444 symbolic steps in total (maximum 39).
* `KControlFrame.controlSuffix_frame`: suffix-local strip/increment checks imply
  the exact source action for every prefix and every register function.
* `KFramedControl215.all_aligned`: ordinary kernel reduction checks all 35 links
  between runtime inputs/outputs, entry-state numerals and source suffix actions.
  This checks the state supplied to each local body; it does not prove that the
  decoder routes every source occurrence to that state.
* `KFramedControl215.control_contract`: each template gives the exact whole-tape
  runtime contract and source `execute` equation together. The exact output gap
  is `n + 16 + |suffix| - |result|`; the register file is unchanged.
* `FrameAudit.lean` independently states the final whole-tape endpoint, source
  equation, guard counterexample and exhaustive template index list.

The source action theorem is supplied by the companion `KControlFrame` component.
The runtime semantics, transition table and Home proof are unchanged pinned
repository sources. Six dependency copies are listed in `SOURCE_PINS.json`.

The Home composition retains the existing `BoxLemmas`, scanner rows and boundary
contracts as explicit parameters. At integration those are the already established
K215 engine lemmas. The caller prefix must satisfy the existing finite `scanBound`
predicate. Its final bit can be zero. The far-left exterior is blank, as required
by Home; this is not an arbitrary exterior theorem.

## Replay

From this directory, with the repository-pinned Lean 4.32.0 executable:

```sh
python3 replay.py --lean /absolute/path/to/lean --out /tmp/k215-frame-replay
```

The output directory must initially be empty. The driver copies and checks the
exact 10-project-module closure plus the closed client, uses only its own freshly
produced project objects, honors `/tmp/proveit-k215-proof-build.lock`, rejects
compiler errors, new-module warnings and disallowed axioms, and records sources, direct
dependency objects, compiler identity, logs and exit statuses. This small closure
has only Lean's shipped `Init` as an external import boundary.

Inherited dependency warnings are recorded separately. The first fresh replay
stopped because an unnecessarily strict gate rejected the existing `KZip` unused
simp warning; that failed gate and driver remain in `history/replay-gate-attempt1`.
The final driver records compiler wall time separately from shared-lock waiting.
It does not measure or claim a production build speed improvement.

Data generation is untrusted. To reproduce it:

```sh
python3 generate_templates.py data/FORMAL_TEMPLATES.json
python3 generate_control_templates.py data/FORMAL_TEMPLATES.json
```

Both generation checks reproduce exact checked source bytes. No `native_decide`,
new axiom, or admitted proof is used. The final runtime theorem uses the standard
Lean assumptions `propext`, `Classical.choice`, `Quot.sound`; the finite equations
are separately audited.

## Integration still required

The independent finite source audit associates 1,422 of the 6,176 outcomes with
these templates. This component kernel-checks the universal templates, not those
1,422 source-occurrence routing instantiations. Integrating them requires a typed
occurrence descriptor/coverage gate, the decoder-prefix adapter and the literal
fallback checks, followed by the complete endpoint check. The proposed reduction
from 6,176 to 4,789 expensive local executions is an obligation count inherited
from the earlier proposal; it is not a newly measured production size/time saving.

The four new Lean modules occupy 575 lines and 31,899 bytes before integration.
This is added proof infrastructure. A net shortening must count removed
production checks, retained fallbacks and generators after integration.

## Provenance

Repository snapshot: `cbf94cb552a3b49509e0eee80e7455d4eb5974c6`.

The 35 template choices and formal labels come from the repository's existing
`verification/k215/simplification/proposals/round13-left-frame/runtime/FORMAL_TEMPLATES.json`
(SHA-256 `e2b8fd178afba6c85edf17eb647751d90a606541f03b01b76ec309acfdd62238`).
The new contribution is the checked frame/action/composition theorem and the
actual-table kernel checks, not rediscovery of those 35 templates.

Preserve the original notices and applicable licenses when incorporating the
unchanged dependency copies. Development failures are kept outside accepted
fresh-replay evidence.
