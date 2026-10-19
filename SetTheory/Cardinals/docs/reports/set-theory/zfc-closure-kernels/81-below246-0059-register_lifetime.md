# Register lifetime sharing and a matched eight-register codec experiment

2026-10-16. The tested eight-register representation costs **306 working
states** after a bounded 32-layout emitter experiment; it does not improve the
retained complete-calculus controls. The same compiler reproduces the original
nine-register program at **281 = 219 + 62** states. No candidate table or Lean
baseline was changed. No new calibrated consistency machine is claimed.

The inputs are Mira-Cult's 219-node program, Jeff's verification snapshot
`297ab8df7e5de329605c3875b4934643b371a5e3`, and Wade's public TMBuilder. The
program source is the unchanged vendored `ZF/m254/coq/prog/Dag254.v`, SHA256
`538ddaddd932058c2b319011126579d77783231f54331772377c05848a0599e3`.
The unavailable author `source.py` is not reconstructed. The CFG calculation
reuses source08's finite path interpreter; grammar sampling reuses the
repository's overlap-safe Re-Pair implementation. The new algorithms and
measurements are in [register_lifetime_experiment.py](register_lifetime_experiment.py);
the complete bounded results are in
[results/register-lifetime-experiment.json](results/register-lifetime-experiment.json).

## What prevents a direct lifetime allocation

The logical registers are `N,T,W,A,D,H,X,Y,L`, respectively next candidate,
current formula, formula stack, command/matrix, parameter, cache, two scratch
counters, and remaining command word. The exact layout is in
`Lean/BusyBeaver/ZFC/L2Lib254.lean:21`.

An increment reads the previous value of its target. Treating increments as
ordinary assignment kills would produce an unsound interference graph. At the
other extreme, treating every decrement loop as an ordinary branch misses true
kills. The checked macro contracts distinguish these cases:

| Operation | Exact effect relevant to lifetime |
|---|---|
| clear199 / clear214 | `H := 0` / `T := 0`; old contents are dead |
| transfer201 / 203 / 205 / 207 / 208 | `X` is consumed; destination receives its old value plus `X` |
| transfer209 / 211 / 212 | `Y` is consumed; destination receives its old value plus `Y` |
| copy193 / 198 / 200 | source `A/D/H` is consumed and added to both `X` and `T`; a subsequent transfer restores the parameter |
| pair162 | consumes `X,T`, adds `P(X,T)` into `Y` |
| loop115 | preserves `N,T,W,A,D,H`; returns `unP(P(X,Y)+L)` in `X,Y`, with `L := 0` |

These are actual Lean theorems, not inferred instruction names; see
`L2Lib254.lean:135` through `:195`, `:249`, `:349`, `:388` and
`L2Macros254.lean:49` through `:87`. In particular, the second command-field
read preserves the already decoded command/matrix as well as the six
persistent values (`L2Root254.lean:128`).

The shared Cantor unpair loop is a concrete local obstacle. Start its exact
macro contract with

```
N,T,W,A,D,H,X,Y,L = 101,103,107,109,113,127,0,0,1000.
```

After 100 walk iterations its values are

```
101,103,107,109,113,127,4,9,900.
```

All nine stored values differ. The six outer fields must be preserved. The
remaining result depends on each of `X,Y,L`: `P(4,9)+900=1000`, whereas changing
just one counter by one gives 1014, 1015, or 1001. Thus an allocator preserving
this full macro interface cannot identify any of the nine simultaneously
stored values. This remains true after acknowledging all genuine clear and
transfer kills. Recomputing or packing values changes the algorithm and is a
different opportunity.

This example satisfies the checked macro's hypotheses. **Reachability from
blank tape or from a valid proof invariant is not asserted.** It therefore
does not rule out an allocation justified by a stronger invariant of the
whole enumerator, much less arbitrary eight-register implementations.

For context, exact unfolding gives 6,460 instruction leaves, 4,533 reachable
operation sites after contracting break/continue, and maximum path length96.
A deliberately conservative backwards use calculation finds all nine inputs
live at the 4,532 nonhalt sites. That calculation has no clear-loop summaries
and supplies no register lower bound; the local macro contract above is the
sharper evidence.

## A different representation that uses eight registers

Use the total bijection

```
E(a,b) = 2^a (2b+1) - 1.
```

Here `E(0,0)=0`, so the nil/zero-stream convention and formula target
`Rel(0,0)=1` remain intact. Both components of `unE(n)` are at most `n`.
For positive formula codes the usual base-four tag gives the strict component
bounds needed for finite parsing and the self-code freshness argument.
These algebraic observations are ordinary mathematics, not a new Lean codec
theorem. All arithmetic uses exact Python integers; no numerical fingerprints
stand in for very large AX formulas.

Only `X` is needed by the new primitive routines:

* An additive field read first increments the source. Repeated division by two
  counts the exponent directly into its destination. Each even half restores
  the source and clears `X` before continuing. The final odd half supplies the
  tail. This avoids retaining a separate unpaired head.
* Push starts with `W := 2W+1`, consumes `T` while doubling `W` once per unit,
  then decrements `W`.
* Fused cons starts with `T := 2T+1`; each factor of two extracted from `W+1`
  doubles `T`. The final odd quotient gives the stack tail. Decrementing `T`
  and multiplying by four gives `Imp(head,old_T)` without storing the head.
* A nondestructive comparison of `A,H` counts matched decrements in `X`,
  restores `A`, consumes `H`, and clears `T` exactly on equality. Applying it
  before and after moving `D` into `H` implements both original freshness
  tests, then clears `A`. This removes the final use of `Y` in the old gate.

The generic source-35 `read158;move208` is fused into an additive read into
`T`. All reachable primitive edges are checked to avoid `scratch2`; the final
compiler declares exactly eight physical registers. Register names in the
saved logical DAG still use the original naming convention; `prooflist` is
the eighth physical declaration rather than the ninth.

The entire GEN + eight logical rows and original CP/GIC/native-equality/
vacuity bundle are retained. The driver compares the actual modified AX
expansion with the checked full macro word, and maps its fused read and new
gate back to the exact original word. The symbolic rows equal the original
rows **under the new pair interpretation**, not as old numerical Cantor
codes. MP, DROP, NIP, the two gates, and the exhaustive-candidate shell all
remain present. No weaker theory or partial emitter is substituted.

## Complete compiler costs and limits

| Representation | Registers | Unshared complete control | Best of32 layouts | Best decision + framework |
|---|---:|---:|---:|---:|
| original Cantor everywhere | 9 | 281 | not rerun | 219 +62 (unshared) |
| 2-adic everywhere | 8 | 313 | 306 | 244 +62 |
| 2-adic command words only | 9 | 300 | 293 | 230 +63 |
| 2-adic stacks only; Cantor formulas | 9 | 303 | 296 | 232 +64 |
| 2-adic words and stacks; Cantor formulas | 9 | 315 | 308 | 244 +64 |

Every count comes from an actual compiled table and includes the generic Wade
bootstrap, selectors, dispatcher, arithmetic runtime, complete emitter, gates,
and command loop. Every decision edge is independently re-extracted from the
compiler output. The framework is counted per table; it is not assumed
constant. In these layouts, the longer dispatcher offsets the selector saving.
The saved complete tables totalize the backend's single missing `1.inc/1` row
to halt, using the repository's existing convention.

Each lane samples exactly seeds0–31, exponent2, with exact word expansion
checked for every layout. The grammar terminal alphabet is remapped before
sampling so newly allocated macro IDs cannot collide with grammar variables.
There is no exhaustive-layout or optimality claim. The existing complete
268-state old-code control remains better than every candidate here.

The finite exact-register suites pass 898 cases for the eight-register lane,
294 for command words, 330 for stacks, and 474 for the combined hybrid. They
include matched encoder/decoder operations, additive reads, fused cons,
preserving comparison, both freshness gates, all three non-AX command branches
against an independent one-step spec, literal NIP halts, and fetch. AX's
enormous new integer outputs are checked symbolically, not by a finite full AX
numeric run. These tests and source comparisons are not formal macro proofs.

The bootstrap is charged but its new clean/dirty startup invariant is
unverified. There is no new whole-program simulation, binary runtime proof,
codec/calculus transport, or ZFC calibration. The experiment is a negative
measured result for these recipes; the frozen 252-state candidate is untouched.

Reproduce offline, without Lean:

```sh
uv run --no-project python Computability/BusyBeaver/Research/ZFC/register_lifetime_experiment.py \
  --scratch /tmp/zfc-register-lifetime-replay \
  --output /tmp/zfc-register-lifetime-replay/results.json
```
## Batch155 comparison

Source46 in `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels`
uses future zero-register markers as temporary initializer counter bits and
restores them before dispatch. Its complete299/300-state controls are reproduced;
this lifetime reuse occurs during initialization and does not contradict the
nine-live-interface observation above. Source45's22/24-control name transports
are separate calculus interfaces whose complete backend costs remain unmeasured.


