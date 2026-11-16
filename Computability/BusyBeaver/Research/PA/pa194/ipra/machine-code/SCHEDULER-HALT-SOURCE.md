# Scheduler halt at a source command boundary

Fetch, decode and tag dispatch preserve the top, stack, proof argument and
cache registers. The strengthened prefix also retains the command suffix,
next scheduler enumeration counter and cleared scratch registers. The
earlier theorem statements are projections of these results.

`PA194ShiftModelHalt.halt_of_sum_one` checks two finite SHIFT paths from site
3661 with a zero scratch register. The paths take 17 steps for top one and
cache zero, and 18 for top zero and cache one. The other registers and file
suffix can hold arbitrary elements of a PRA model with classical IΣ₁
arithmetic reduct.

`PA194SchedulerHaltSource.haltFromRoot` combines the actual source fetch with
SHIFT. At an aligned site-25 boundary it converts the scheduler halt flag
to a controller run reaching the absorbing PC 3674. Returning to the next
aligned site-25 root after an ordinary command remains a separate obligation.

Run from the repository root with the staged outputs listed in
[SCHEDULER-BRANCHES-OPEN.md](SCHEDULER-BRANCHES-OPEN.md) available.

```sh
bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-scheduler-halt-source.sh /dev/shm/pa194-scheduler-halt-source-new
```

The four repository sources replayed in a single output with no `sorryAx`
or `Lean.ofReduceBool` in the reported axioms. Lower imports use the retained
fetch, decoder and arithmetic stages.

`PA194SourceSchedulerOrbit.synchronize` uses IΣ₁ induction to align any
model length of ordinary commands with source execution. It carries the
controller clock as an existential witness and uses the positive length of
each command to bound that clock below by the scheduler index. Since the
controller's halt state is absorbing, a segment whose endpoint is a normal
root cannot have halted in its interior.

`PA194SchedulerSourceFrame` checks the packed frame at the exact initial
states of both programs and applies the local halt theorem at that frame.
Its `equivalent_of_return` gives the model-level correspondence between
controller halting and scheduler halting assuming that every command with a
clear halt flag reaches the next scheduler frame in positive time.

Both modules replayed from repository sources and reported only ordinary
Lean axioms. Run the orbit checker with the previous four-source scheduler
stage and the compressed-controller stages in place.

```sh
bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-scheduler-source-orbit.sh /dev/shm/pa194-source-scheduler-orbit-new
```
