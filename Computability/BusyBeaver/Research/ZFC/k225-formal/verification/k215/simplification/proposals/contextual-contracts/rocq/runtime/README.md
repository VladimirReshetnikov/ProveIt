# Guarded framing of the actual K215 symbolic runtime

This component proves that the current `Runtime230Core.sstep` commutes with
an arbitrary appended symbolic left context whenever the step does not expose
an empty left boundary. It then checks all 35 local return templates from the
repository's earlier round-13 proposal and lifts them to arbitrary contexts.

## Checked interface

`add_left F (q,onl,l,r) = (q,onl,l ++ F,r)`. The guard `safe_left s` is false
exactly when `onl = true` and the left list is empty. The generic theorem
`sstep_natural` says, under that guard, that framing commutes with one actual
symbolic step. An unguarded version is false; `unsafe_frame_counterexample`
checks a counterexample using the actual transition table.

`run_local` performs a fixed number of symbolic steps, checking the guard at
each step. `run_local_frame` proves that every successful local replay remains
valid after an arbitrary symbolic left frame is appended. No bound is placed
on that frame, register values, or the symbolic gap parameter.

`LeftFrame215.template_replay` applies this result to each of the 35 literal
templates. The finite computation covers 444 symbolic steps in total. The
endpoint has state 2, left orientation, and an empty local left side; appending
a frame supplies exactly the left context for a later Home lemma. The template
module does not compose the Home step or claim positive machine progress.

`run_local_sound` connects the guarded replay to the actual machine's
reflexive transitive reachability, for arbitrary gap parameter and valid
register file. It retains the four explicit box-correctness premises required
by the inherited `sstep_sound` theorem (`box_mark`, `box_inc`, `box_dec0`, and
`box_decp`). These are theorem premises, not global axioms. Production already
provides the corresponding box theorems; this component does not import or
rebuild their modules.

## Exact verification scope

The accepted evidence has two separate stages, both with Coq 8.18.0 / OCaml
4.14.1:

1. `evidence/core/result.json`: all nine source modules through `LeftFrame.v`
   were freshly compiled; four selected assumption reports are closed, and
   recursive `coqchk Refactor.LeftFrame` passed.
2. `evidence/templates/result.json`: the final `LeftFrame215.v` was freshly
   compiled against those exact nine source/object dependencies; two selected
   assumption reports are closed. The receipt hashes the reused baseline
   receipt and every reused object. This final template module was checked by
   `coqc`; no separate recursive `coqchk` was run on that added module.

The first recorded template draft failed to compile; its receipt and raw log
are kept under `evidence/development/`. They do not describe the delivered
source. The final template receipt does. This history is not an additional
successful check.

The portable `build.py` now replays all ten modules from source and runs a
recursive check of the final template module. That combined driver is supplied
for reproduction; the delivered accepted receipts record the two stages above,
not a later single combined execution. The production Rocq 9.1.0 lane and the
complete ZFC endpoint were not rebuilt.

## Provenance and reproduction

All eight inherited dependencies are byte-identical to their pinned repository
files. There are no import rewrites or compatibility shims. The five K215
runtime files are the current production files; the three BusyCoq files are
the repository-vendored adapter snapshots. Exact paths and hashes appear in
`SOURCE_PINS.json`.

The JSON input is copied byte-for-byte from
`verification/k215/simplification/proposals/round13-left-frame/runtime/FORMAL_TEMPLATES.json`
at ProveIt commit `cbf94cb552a3b49509e0eee80e7455d4eb5974c6`.
The generator emits finite literal data and a standard proof wrapper. Correct
execution is established by reduction against the actual `sstep`, followed by
the generic theorem; the generator and JSON trace annotations are not trusted
as semantic oracles. This component does not prove that the template set
covers every production control-node obligation.

With `coqc` and `coqchk` available:

```sh
python3 generate_templates.py inputs/FORMAL_TEMPLATES.json --output /tmp/LeftFrame215.generated.v
cmp /tmp/LeftFrame215.generated.v src/Refactor/LeftFrame215.v
python3 build.py --out /tmp/k215-left-frame-fresh
```

For an unpacked Ubuntu Coq installation with an `ocamlfind.conf` pointing at
its own `usr/lib/ocaml`, add `--toolchain /absolute/path/to/toolchain` to the
build command. The output directory must be fresh. The inherited `Boot230`
contains a large literal startup reduction, so its compilation and recursive
checking can take much longer than the new frame proof.

## Attribution

The finite template data and left-frame proposal originate in the repository's
round-13 work. This packet supplies an axiom-free proof against the current
Rocq runtime, the boundary counterexample, and checked concrete templates.
Inherited files retain their original licenses and attribution; see
`licenses/`. New proof and documentation material follows ProveIt's MIT No
Attribution terms.
