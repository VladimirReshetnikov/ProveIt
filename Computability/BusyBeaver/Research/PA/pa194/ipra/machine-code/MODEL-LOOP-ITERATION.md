# Conditional model-length loop iteration

`PA194ModelLoopIteration.modelIteration` is a generic, exact-clock iteration
schema for the packed literal-machine stepper. For fixed primitive-recursive
codes `next`, `cost`, and `frame`, it defines primitive-recursive `iterCode`
for repeated state updates and `timeCode` for their accumulated cost. The
open invariant says that either the current iteration is beyond a model-valued
bound or running for the coded accumulated cost reaches the coded frame for
the current state. Model open induction proves the stated equality for every
model-valued number of iterations at most the bound, including nonstandard
values.

The essential hypothesis is a *model-level* universally quantified one-step
physical equality for every i below the bound, using `cost(iterCode(i,start))`
and `frame(iterCode(i,start))`. The result is conditional on that equality;
it does not identify the PA194 loop's concrete state, frame, or cost codes,
does not yet derive an internal PRA or native iPRA sentence, and is not an
unbounded source/machine simulation. The proof applies to each PRA model via
its existing open-induction result, and assumes no additional IΣ₁ hypothesis.
The PA194 loop additionally needs primitive-recursive codes for its concrete
state layout and per-step physical clock, and a proof that its branch and
one-step equalities meet this hypothesis.

`PA194ModelLoopState.iterPacked` supplies a partial concrete state update:
for any supplied primitive-recursive controller advance, model iteration
increases the gap by `i` and the spare count by `2*i`, preserves the spare,
and iterates the supplied controller advance `i` times. It does not yet supply
the concrete frame, cost, or guarded physical one-step equality.

Replay with `check-model-loop-iteration.sh` into a fresh output directory;
the usage lists its roots. `ROUNDTRIP_STAGE` is the successfully audited
`check-one-spare-file-roundtrip.sh` output. It pins the existing iterator
object, rebuilds the new source, checks all printed axioms for `sorryAx`, and
checks retained inputs for changes. This is a staged check and does not rebuild
the full transitive source closure of the retained roots.
