# AX11H nonhalting SHIFT and returning commands

[The SHIFT theorem](PA194AX11HShiftFrame.lean) verifies a strictly positive
source run from the concrete scheduler frame to its next frame when the
fetched opcode is zero and the halt flag is clear. The revised source
copies the old cache to the top, clears the cache during the guard, and
decodes the old Cantor stack into the new cache and stack.

[The returning-command theorem](PA194AX11HReturningCommands.lean) splits
the modeled opcode into SHIFT, modus ponens, and axiom cases. It applies
the checked SHIFT and modus ponens theorems and takes the exact axiom
frame step as its remaining premise.

Run from the repository root with the checked [halt-frame](README-halt-frame.md)
and [concrete MP](README-mp-scheduler-link.md) stages.

```sh
variant=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa194ax11h
bash "$variant/check-shift-frame.sh" /dev/shm/pa194-ax11h-halt-frame-repo /dev/shm/pa194-ax11h-mp-link-repo /dev/shm/pa194-ax11h-shift-frame
```
