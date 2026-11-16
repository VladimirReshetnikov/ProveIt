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
