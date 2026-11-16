# AX11H cache-only halt command

[The flag theorem](PA194AX11HCacheFlag.lean) proves that the exact cache-only
scheduler flag is one when the fetched opcode is zero and the cache field
is one. [The command proof](PA194AX11HHaltCommand.lean) follows those
conditions through the revised source. It clears the old top, copies the
cache to the top, restores the cache, and reaches source site 10 through
the halt test at site 0.

[`PA194AX11HHaltFrame.fromFlag`](PA194AX11HHaltFrame.lean) composes the
checked fetch with the halt command. In every covered arithmetic model,
it reaches site 10 from the exact scheduler frame whenever the
`haltAtK true` flag is one.

Run from the repository root with the checked scheduler core and
[fetch and scheduler-frame stage](README-mp-frame.md).

```sh
variant=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa194ax11h
bash "$variant/check-halt-frame.sh" /dev/shm/pa194-scheduler-core-repo /dev/shm/pa194-ax11h-mp-frame-repo /dev/shm/pa194-ax11h-halt-frame
```
