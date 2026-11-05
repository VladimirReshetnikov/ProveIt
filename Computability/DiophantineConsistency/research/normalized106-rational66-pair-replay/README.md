# Same-source replay of the historical 66/106 pair

This replay compiled the unchanged source from
`../normalized106-rational66-pair/` against the same captured historical
provider objects, at a fresh output path. Lean and runner exited 0; the
output object and complete compiler/axiom log are byte-identical to the
original successful run. No warnings or `sorryAx` were reported. The
runner pinned the original object, log, child receipt and separately
observed outer exit as well as the 66→specialization→actual chain and the
historical stage-078/079 producer inventories. Its 676 recorded guard
entries were stable.

The replay used `-M2800`, a 120-second timeout, sampled 3.5 GiB group RSS
and a 10 GiB available-memory floor, nice 19 and idle I/O. It took 2.335
seconds, with peak sampled RSS 2,834,583,552 bytes and minimum available
memory 18,865,070,080 bytes. Outer session 32461 was directly observed
to exit 0; that observation is retained separately from the child receipt.
This is a same-provider replay, **not** a fresh source-closure rebuild or
an independent audit of inherited package/dynamic ancestry.

The theorem pairs an external actual-port 66-row rational zero iff with
the existing iPRA theorem about the 67/106 integer syntax. It does not
prove an internal rational-leaf sentence or a 66-operation integer-leaf
equation. The original and replayed object both have SHA-256
`7eb1409fde81bbc8fb224242dd71e575db55562fb7704764109d20e085c74a37`, and
their complete log hash is
`e8a74c471b99f513888eb6fd1c7b7e3d2df715c51ed945f3a8f4865112ce342f`.

| Artifact | SHA-256 |
| --- | --- |
| `check01.py` | `5d809f37ad1c43b190b377df92081037e45d34a365db2e0c81fd071fe269e52d` |
| `observations/attempt01/compile.log` | `e8a74c471b99f513888eb6fd1c7b7e3d2df715c51ed945f3a8f4865112ce342f` |
| `observations/attempt01/result.json` | `d46f16e4147b8856ff8a315ec28f379202579a3d993e05efc766ce8e6cfebe76` |
| `observations/attempt01/outer-terminal.json` | `0ff555a435ade1c1f406fdd8d3abddce2ed9d856599b65b1aba20b7e5d6304de` |
