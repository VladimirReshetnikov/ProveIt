# A short, checked transfer proof for CM215

This packet addresses the proof-simplification part of the ZFC Busy Beaver
project. **The machine is the existing conditional-marker CM215 alternative;
it is not a newly discovered machine and is not a 214-state construction.**
The new result is a compact, independently checked transfer proof.

## Main result

`CM215Exact.blank_equihalt` proves exact blank halting equivalence of the
primary K215 native table and the existing CM215 native table. Its stronger
parent `CM215Exact.all_tapes_equihalt` holds for every two-way binary tape and
every head position, with initial control 0. It is not an arbitrary-control
simulation theorem: a marker invariant is needed away from the start.

`CM215Core.blank_halts_iff_primary` additionally proves, in the repository's
unchanged `Machine 215` / `BlankHalts` semantics, that the literal CM215 dense
machine halts if and only if the exact original `KDense215.machine215` halts.
The direct tape-embedding bridge and both all-row compatibility decisions
were also compiled in this session. The full-ZFC transitivity adapter was
not compiled here; it requires the existing complete ZFC closure.

The exact table counts, closure, incoming-edge facts, invariant induction,
local simulation and global halting equivalence are checked by Lean 4.32.0.
The final native equivalence reports only `propext` and `Quot.sound`; finite
facts report only `propext`. There is no `sorry`, `axiom`, `admit`,
`native_decide`, or trust in the Python certificate in these theorems.

The full native label range includes 301 and 302. The ambient type `Fin 303`
merely accommodates those names. The kernel proves that exactly 215 labels
have outgoing transitions, that both binary rows exist at each such label,
and that all targets are working labels or the separate halt 254. Thus the
ambient type does not hide additional working states.

## Why this alternative is easier to certify

The primary proof's numerical-calculus/ZFC calibration, source compiler,
register engine, source-site certificates and long blank bootstrap are
reused through its established endpoint. CM215 needs only a local theorem
about six changed rows. No new axiom sampler, source program, proof-number
schedule, protected-tail argument, or initial register frame is needed.

This is an incremental proof advantage. The entire foundation shared with
K215 does not disappear. Primary K215 remains the natural canonical baseline.
The small alternative proof is valuable because future physical rewrites can
reuse the same transfer interface, instead of reproducing all 6,176 symbolic
primitive cases for every new machine.

The alternatives involving zero spares or direct transfer have fewer or
shorter physical instructions in some places, but require additional source
or startup theorems. Counting changed transition rows is therefore a poor
measure of proof difficulty.

## The invariant that makes the proof small

For an old-machine configuration `(q,h,t)` put

```
Inv(q,h,t) :=
  (q = 52  -> t(h-1) = 1) /\
  (q = 176 -> t(h) = 0 -> t(h-1) = 0) /\
  (q = 156 -> t(h+1) = 1).
```

The first two clauses express the marker property in the original report.
The third clause is an auxiliary invariant that removes the need to reason
about the previous two transitions. Its only incoming edge is
`189/1 = 1 L 156`, so it holds after every old step. The exceptional incoming
edge `156/1 -> 176` can then be handled by a single inductive step: it returns
to a cell known to contain 1, so it cannot violate the zero-branch marker
condition at 176.

This is a useful proof-engineering pattern: expose one additional local fact
at the predecessor control, making a history-dependent explanation into an
inductive invariant over the current configuration.

The state relation is `phi(176)=52`, with every other label unchanged. The
entire tape and head are identical at synchronization boundaries. Old rows
52/0 and 176/0 are simulated by three new steps:

```
52, current=0, left=1:  52 -> 176 -> 129 -> 154
176,current=0, left=0:  52 -> 176 -> 185 -> 168
```

The moves are L,R,R. All three writes preserve the symbols read. Every other
old transition is simulated by one new transition, including the common
one-branch of 52 and 176.

## The generic theorem

`PositiveSimulation.halts_iff` works for any two deterministic totalized
transition systems. If related configurations have equivalent halting
predicates, each old step has a positive finite target simulation, and target
halting is stable under its next operation, then eventual halting is
identical. Neither a uniform time bound nor a reverse simulation is required.

The proof constructs, for every old time n, a target time k >= n with related
states. Forward halting follows at a synchronization boundary. If the target
has halted by time n, it is still halted at time k, forcing old halting by n.
The positivity requirement is essential: allowing empty target simulations
would invalidate this converse.

For CM215 the target times additionally satisfy n <= k <= 3n; this bound is
not needed by the generic theorem. The machine-specific proof is separated
from the time-change argument and from literal table data.

## Files and trust boundaries

- `PositiveSimulation.lean`: reusable positive-step theorem, using `Std` only.
- `MarkerTransfer.lean`: arbitrary-tape semantics, the three-clause invariant,
  its preservation, exact local simulation and global transfer from start 0.
- `CM215Exact.lean`: complete pinned literal native tables; finite facts are
  kernel `decide`; exact state counts and all-tape/blank equivalence.
- `CoreNativeBridge.lean`: bridge to the repository's unchanged dense machine
  semantics, with a finite-support tape embedded into a total tape function.
- `CM215Core.lean`: literal CM215 `Machine 215`, exact dense/native row
  compatibility, and transfer to the original `KDense215.machine215`.
- `CM215ZFCAdapter.lean`: the two-line transitivity adapter to the existing ZFC
  endpoint, deliberately separate from the small standalone build. It needs
  the repository's complete already verified ZFC dependency closure.
- `vendor/`: six unchanged, hash-pinned repository modules and their MIT-0
  license, sufficient for the dense transfer without the full ZFC project.
- `check_marker_certificate.py`: an independently implemented finite local
  corroboration; not part of the kernel trust boundary.
- `generate_tables.py`: reproducibly transcribes the two native tables into
  literal Lean data; the generated data is checked by the kernel.
- `prepare_core.py`: copies the pinned core dependencies and builds the dense
  data from the canonicalization maps; needs a repository checkout only if
  regenerating that subset.
- `build.py`: serial standalone build and per-module log/source-hash capture.

The two exact native SHA-256 values are:

```
K215  9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2
CM215 e5907f08e0752eada0e25bbf33680341e80e5fe94b52b409aea1ed039edda252
```

`upstream-pins.json` identifies the exact repository commit and six copied
modules. Literal machine files retain their original upstream headers. See
`NOTICE.md` for attribution; no novelty is claimed for CM215's six-row rewrite.

## Reproduce

Use Python 3 and Lean 4.32.0. No mathlib, network access or external solver is
required once this packet and that Lean release are available.

```sh
python3 check_marker_certificate.py
python3 generate_tables.py
python3 build.py --lean /path/to/lean-4.32.0/bin/lean --out /new/build-directory
```

The build runs exactly one Lean process at a time and fails on nonzero status
or any `sorryAx` report. The finite corroboration checks all 6,912 assignments
to the five cells at offsets -2 through 2 and all 215 working controls plus
halt. Exactly 6,872 assignments satisfy the invariant and are verified. The
40 rejected assignments are excluded by the inductive invariant, not by
observations about a particular blank run. No step reads outside that window,
so uninspected cells are untouched; the Lean theorem itself quantifies full
tape functions and does not rely on this finite checker.

To add the ZFC adapter, make the packet modules available to the repository's
Lean search path, use the original repository modules in preference to the
identical vendored copies, and build `CM215ZFCAdapter.lean` after the existing
`BusyBeaver.ZFC.KEndpoint215` closure. The adapter has not been counted as part
of the standalone compiled result. No internal PA formalization or absolute
nonhalting theorem is asserted.
