# Branch once at the register oracle

Revision: `cbf94cb552a3b49509e0eee80e7455d4eb5974c6`.

## New result

For a decrement site, run the branch-independent physical computation once,
stop immediately before the zero/nonzero register oracle, and check the two
continuations from that exact configuration. Do not replay the whole neutral
prefix under both branch assumptions.

This is distinct from earlier source-graph normalization, decoder-prefix reuse,
and the 35 control-return templates. It applies to all 1,425 decrement sites,
including the 2,850 arithmetic outcomes left literal by the earlier control
proposal. It can be adopted directly in the maintained whole-site checkers,
without integrating the older decoder-residual proposal first.

The new proof surface is unusually small: instantiate the existing executor
soundness theorem twice and compose positive reachability with reachability.
There is no new tape representation, symbolic step rule, register lemma,
source bisimulation, or induction over machine runs. A semantic
branch-noninterference theorem is unnecessary: the neutral prefix is proved
correct for every register file directly.

## Precise contract

Let `E` be the existing executor, `C(n,vs,s)` its concretization, and let
`Valid br vs` be the existing branch validity condition. Assume

1. `E none cut f s false = some c`;
2. `E br target g c true = some t`;
3. `Valid br vs`.

Then `target t = true` and `C(n,vs,s)` reaches `C(n,vs,t)` in a positive
number of concrete steps, for every `n` and every such `vs`.

Proof: condition 3 implies `Valid none vs`, since both require at least ten
registers and the neutral branch has no zero/nonzero restriction. The first
existing `exec_sound` gives positive reachability because its initial progress
flag is false. The second gives ordinary reachability because its initial flag
is true. Compose them. Existing `sMatches_conc` / `matches_conc` turns the final
symbolic match into equality of whole concrete configurations. All arbitrary
gap parameters, register values, and spare tails remain quantified.

The useful decidable cut is EXACTLY `(0, false, L, [box(mark r)])`, with `r`
the physical register `physOf logicalRegister`. Both continuations retain the
entire `L`; neither the source path nor its context is discarded. The zero
branch is `some(r,true)` and the positive branch is `some(r,false)`.

The executor must test the explicit cut BEFORE taking a step. Failure of the
neutral oracle is not a valid generic stopping rule: `sstep` can fall back to
the table's `M q false` transition. The synthetic fallback control verifies
this distinction. Starting the prefix with progress=true would also be wrong:
an immediate cut could falsely supply the positive-progress premise.

## Reproducible finite accounting

The new Python checker independently transcribes the inspected symbolic rules.
It parses and equates the current Rocq and Lean tables (430 defined rows),
checks the exact native/formal label map, equates both 179-node source programs,
regenerates all 4,751 source leaves, and binds every inherited site and decoder
port to the current role graph. It then replays both full decrement outcomes,
finds the exact first differing step, and independently replays the proposed
neutral-prefix-plus-two-tails execution. Every prefix is positive.

Abstract step-function calls for the 1,425 decrement pairs only:

- Maintained Lean: `KSim.start` with `KHomeReady.stepper`:
  514,073 before; 312,947 after; 201,126 saved, 39.12%.
- Maintained Rocq: `Interpreter230Sites.start` with the original `sstep`,
  WITHOUT a Home shortcut:
  1,337,729 before; 852,647 after; 485,082 saved, 36.26%.
- Optional prior decoder-residual route: exact `leafPort` with Home:
  415,205 before; 263,513 after; 151,692 saved, 36.53%.

The third line is not the maintained endpoint baseline. The first two stand
alone. Different absolute values reflect different starts and steppers.
The residual prefixes have 36--161 abstract steps and two Home shortcuts each.

These are finite algorithmic operation counts, NOT compiler timings, kernel
proof-object sizes, or total endpoint cost. We count successful abstract-step
calls, not target-predicate evaluations or target-normalization work. There
are 1,425 additional successful prefix-cut checks. All 4,751 leaves and 6,176
guarded source outcomes remain covered; there is no claimed reduction in their
number, no change of machine, and no strengthened consistency claim.

An explicit `match` binds the cut for the two continuations in the proposed
checker. This is a source-level sharing opportunity, not a guarantee that a
particular reduction engine shares all kernel computation. If necessary,
generate named, independently certified cutpoints so each prefix equation is
checked once and opaque thereafter. Measure full compilation and recursive
checking before claiming a speedup; account for the new definitions and lemmas
before claiming a net source-size saving.

## Exact integration points and status

The `inputs/SOURCE_PINS.json` ledger records exact bytes and pinned links.

- `KRuntimeCore.lean`: `Valid` lines 62--66; `sstep` lines 136--163;
  `execWith` 165--171; `execWith_sound` 426--450.
- `KHomeReady.lean`: existing `exec_sound` near lines 92--99.
- `KSim.lean`: `checkEdge` decrement branch lines 66--69; semantic decrement
  case near lines 248--273. Replace its two `runTo` calls by `forkTo`; reuse
  the existing register/target equalities and use `forkTo_sound` in each branch.
- Rocq `Interpreter230Sites.v`: `check_site` decrement branch lines 48--50;
  `site_dec` lines 130--147. Insert the new checker definitions BEFORE
  `check_site` and the lemmas inside the existing `Sound` section. Preserve
  `site_dec`'s exact statement. Replace its two uses of `run_to_sound` by the
  corresponding `fork_to_sound` instance.
- Rocq `Interpreter230Check.v`: `all_leaves_check` must be regenerated and
  checked. It is currently one finite computation over the unchanged leaves.

`proposed/KOracleCut.lean` is a full uncompiled adaptation; `OracleCut.v` is an
uncompiled insertion fragment relying on the existing four box hypotheses.
The Lean module imports only `KHomeReady`, takes fuel explicitly, and belongs
below `KSim` in the dependency graph. `KSim` can import it without a cycle.
`KSim.decnz.fragment.lean` shows the exact changed branch and guards.
Neither compiler was run or installed. No repository program was executed;
only newly authored finite/static checks ran. No public repository was changed.

The changed Boolean checker need not be extensionally equal to the old checker
for arbitrary inputs and fixed fuel: two independently bounded phases change
the search budget. Its universal semantic conclusion is unchanged. Kernel-check
the generic adapters, recompute all leaf certificates, synchronize the maintained
producers/manifests, and rebuild sparse/dense endpoints and dependency reports.
Do not count a failed or missing phase as acceptance. The mathematical proof
above explains soundness but does not substitute for those integration gates.

## Replay

From any working directory:

`python -I -B /path/to/rocq/check_oracle_cut.py`

`python -I -B /path/to/rocq/test_oracle_cut.py`

Both use only the Python standard library and reject optimized Python. They
write deterministic JSON beside themselves. The checker takes about ten seconds
here; that is a diagnostic-runtime observation, not a proof-assistant benchmark.
The 11 boundary/progress controls include wrong state/register/orientation/box,
wrong branch register, false-progress rejection, and the fallback counterexample.

Deliver this directory with its `inputs`, `proposed`, JSON results and scripts.
Do not execute the inherited `.lean` or `.v` inputs as part of the finite replay.
