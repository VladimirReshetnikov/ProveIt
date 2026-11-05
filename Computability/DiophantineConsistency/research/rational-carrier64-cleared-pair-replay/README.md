# Same-source replay of the cleared-pair client

The replay compiled the unchanged source from
`../rational-carrier64-cleared-pair/ClearedCurrentPair.lean` against the
same captured current14 provider objects, with a fresh output path. It
passed with Lean and runner exit 0, no warnings or `sorryAx`, stable
guards, and **byte-identical** output object and complete compiler/axiom
log compared with the original check. It does not rebuild the base or
independently check transitive provider ancestry.

The run used `-M2800`, 120 seconds, sampled 3.5 GiB process-group RSS and
10 GiB minimum available-memory stops, nice 19 and idle I/O. It took 2.446
seconds; peak sampled RSS was 2,837,188,608 bytes and minimum available
memory 18,858,033,152 bytes. Outer session 4597 was separately observed
to exit 0; that observation is retained apart from the child receipt.

The replayed theorem pairs an external actual-port rational zero iff with
an iPRA derivation about an existing cleared **integer-language** sentence.
It does not prove an internal rational-leaf formula or a 64-operation
integer-leaf equation.

The fresh object is
`/tmp/rational-carrier64-cleared-pair-replay-priority-check01/ClearedCurrentPair.olean`,
SHA-256 `6f8afbccd823e06ce3173999dcedab7828abb573d04e7855fa40583298584cdb`;
the original object has the same hash. The complete log hash is
`9b295efdef720cee846b4f420067ae5e4ccfedbf224b67d5bf817ebbbd9e9087` for
both runs. The runner also pins the original object, receipt and outer
observation before launching.

| Artifact | SHA-256 |
| --- | --- |
| `check01.py` | `0ecdc2e6fcaa5809fb2cc2d258d3effd472ca6d9c5afd3d666f1ab3f1ea8b211` |
| `observations/attempt01/compile.log` | `9b295efdef720cee846b4f420067ae5e4ccfedbf224b67d5bf817ebbbd9e9087` |
| `observations/attempt01/result.json` | `631e514d4cb557462890ffd2dd7b8cfacf91f83b8b67205b9f6f5e881d629a51` |
| `observations/attempt01/outer-terminal.json` | `0659fa11615658e93ba817037da27d9bc3415f2af0a127c62a3c6f63248075c0` |
