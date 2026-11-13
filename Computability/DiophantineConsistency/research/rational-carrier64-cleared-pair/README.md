# Actual rational zero equivalence and cleared integer iPRA sentence

`external_and_cleared_ipra` combines two distinct checked propositions at
the actual current14 ports:

1. Externally, the 64-row fixed-rational-leaf evaluator has a strictly
   positive integer zero iff the selected cleared integer expression has
   one, using the same valuation in both directions.
2. Standard iPRA derives the equivalence between the no-zero sentence for
   that selected integer expression and the intuitionistic negation of the
   mapped native ZFC-refutation predicate.

The cleared expression is the existing normalized 65-row integer syntax;
its evaluation was checked against the literal graph and its no-zero
sentence identified definitionally with `noZero14` by the predecessor
client. The rational-to-integer relation is an **external** equality of
ordinary evaluations. There is no rational-leaf object-language term or
iPRA derivation for one here, and the result is not a 64-operation
integer-leaf record or a replacement for the maintained equation/PDF.

Attempt01 passed with Lean and runner exit 0, no warnings or `sorryAx`, and
axiom report `[propext, Classical.choice, Quot.sound]`. The run used
`-M2800`, 120 seconds, sampled 3.5 GiB group RSS and a 10 GiB minimum
available-memory guard, nice 19 and idle I/O. It took 2.446 seconds; peak
sampled RSS was 2,840,403,968 bytes and minimum available memory was
18,850,148,352 bytes. Direct source/object pins, predecessor receipts and
base state were stable. Outer session 53951 was separately observed to
exit 0; its observation is retained independently of the child receipt.
Transitive/dynamic ancestry and sampled monitoring are inherited limits.

The output object is
`/tmp/rational-carrier64-cleared-pair-priority-check01/ClearedCurrentPair.olean`,
SHA-256 `6f8afbccd823e06ce3173999dcedab7828abb573d04e7855fa40583298584cdb`.

| Artifact | SHA-256 |
| --- | --- |
| `ClearedCurrentPair.lean` | `fb35fe4a8c8bfa1995265109485853a7b906728a9e1e87140d096b415be2f079` |
| `check01.py` | `2a2c83e7c504cc47fb2c73ce11f92a28772dba946a1d2f0f4b42f87991ab428f` |
| `observations/attempt01/compile.log` | `9b295efdef720cee846b4f420067ae5e4ccfedbf224b67d5bf817ebbbd9e9087` |
| `observations/attempt01/result.json` | `de1c08b733e08df60462a56f1a3640187106f3400c00654f9b5d198a4ed5e602` |
| `observations/attempt01/outer-terminal.json` | `86b0b1817754f554c1818a5a15e21ae9722238f7c8f7e81f56c0b57d606a5807` |
