# M5 modus ponens at the scheduler frame

The [fetch proof](PA194M5DecodeScheduler.lean) executes the literal
radix-five source from site 25 to site 48 and identifies the decoded
command fields. Its [agreement check](PA194M5FetchAgree.lean) uses the
primary source only at sites 25 through 47. The [dispatch proof](PA194M5MPDispatch.lean)
connects opcode 1 to the command entry at site 3614.

The [coded scheduler branch](PA194M5GenericMPScheduler.lean) gives the
exact modus ponens update and uses radix five in the implication
comparison. [The frame theorem](PA194M5MPFrameScheduler.lean) combines
fetch, dispatch, and the [complete command](../PA194M5MPCommand.lean).
For opcode 1, it reaches the frame of the coded next state from the
canonical input frame in a positive model-valued time. The other
branches are code parameters, so their execution is a separate proof.

Supply the checked [M5 command](../README-constructor.md) stage and
the AX11H [paused field](../../pa194ax11h/README-paused-field.md)
stage, which supplies the primary fetch support. From the repository
root, run

```sh
radix=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa194m5
bash "$radix/mp-frame/check.sh" /path/to/checked-mp-command /path/to/paused-field /path/to/fresh-mp-frame
```
