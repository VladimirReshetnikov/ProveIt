# Model-length site-27 source-controller loop

`PA194ActualSourceRun.sourceRunIteration` proves an exact closed form for the
actual encoded source-controller `run` in every PRA model. Starting at source
site 27 with arbitrary model-valued register values and an independent file
tail, after `4*i` controller steps, for any model-valued `i ≤ initial r0`,
the controller is again at site 27 with registers `r0−i`, `r6+i`, and `r8+i`;
all other source registers and the controller tail are preserved. The proof
includes nonstandard model values of `i`: its register invariant and the
fourfold-step grouping both use open induction in a PRA model. `reachesZero`
specializes to `i = initial r0` and shows the tested register is then zero.
No additional IΣ₁ hypothesis is used.

This is a Lean theorem about every PRA model. It is not yet a native iPRA
sentence, a model-length physical-machine simulation, or either direction of
`Con(PA) ↔ ¬Halt(PA194)`. The one-loop source transition is discharged using
the checked four-step controller/physical loop. The physical iteration schema
also needs primitive-recursive exact loop clocks and their connection to the
coded frame; the four-step physical theorem alone has existential clocks.

`check-actual-source-run.sh` extends the separately passed
`check-dynamic-source-loop.sh` source rebuild with these eight sources, in
order: `PA194ModelLoopIteration`, `PA194ModelLoopState`, `PA194ModelLoopFrame`,
`PA194ModelSourceLoop`, `PA194ModelLoopFour`, `PA194ControllerLoopFrame`,
`PA194ActualSourceLoop`, and `PA194ActualSourceRun`. It pins their source hashes
before and after the rebuild and checks their printed axioms for `sorryAx`.
Supply the 25 arguments for the dynamic-loop checker, followed by the iteration
source directory. The successful replay uses the following staged roots: the 19 arguments in `SEED-CONTROLLER-REACH30.md`,
then `build-site28-dynamic-complete`, `build-site29-dynamic-complete`,
`build-one-spare-file-roundtrip`, and `build-site30-jump` under
`/dev/shm/pa194-site28-work`, followed by
`/dev/shm/pa194-site28-dynamic-controller`,
`/dev/shm/pa194-site29-dynamic-controller`, and
`/dev/shm/pa194-site28-work`.

The combined checker rebuilds the controller/physical source closure and these
new modules in a fresh temporary directory. Its separate physical machine stages,
code-graph overlay, and general foundations are retained prebuilt inputs; their
selected pinned objects and overlaps are audited, but this does not authenticate
their entire transitive source closure. The wider replay passed with exit 0 in `/tmp/pa194-actual-source-run-check.log`.

The repository-source replay also passed using this directory for the source
arguments and the same retained staged roots.

`PA194ActualSourceExit.exitsAt31` extends the model theorem through the
zero branch after `4*r0+1` controller steps. Separately,
`PA194ActualSourceRunSentence.nativeIPRA` proves the universally closed
source-controller equality at site 27 after `4*r0` steps in the native iPRA
theory. `check-actual-source-native.sh` rebuilds and audits both additions; its
independent and repository-source staged replays passed. These statements do
not establish physical-machine iteration or either consistency direction.

`PA194ActualSourceExitSentence.nativeIPRA` additionally proves the universally
closed source-controller equality at site 31 after `4*r0+1` steps.
`PA194ActualLoopOrbit.frameOrbit` identifies the coded site-27 physical frame
along the packed source-state orbit up to the initial `r0`; it is a frame
identity rather than a physical execution theorem. Independent and
repository-source replays of `check-actual-loop-orbit.sh` passed using the
same retained machine, graph and foundation stages.

`PA194ModelLoopCost` builds a primitive-recursive combined cost from supplied
site-27, site-28 and site-29 clock codes and the fixed 40-step jump. The
associated input lemmas identify their packed-state argument vectors and the
next frame. `check-actual-loop-cost-inputs.sh` replays these four modules with
the same staged source closure; its independent and repository-source runs
passed. The concrete segment clock equalities and a complete coded physical
iteration remain separate obligations.
