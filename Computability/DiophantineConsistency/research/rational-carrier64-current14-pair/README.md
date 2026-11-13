# Narrow same-base pair: external rational fact and iPRA endpoint

This checked client states two separate facts in one Lean theorem:
the already checked external actual-port rational zero equivalence, and
the existing standard iPRA theorem about the integer-language `noZero14`
sentence. It does not claim an internal rational-leaf sentence or change the
integer-leaf operation count. Its search path used the fresh current14 base,
the checked rational client chain and the authenticated package provider;
it did not import the historical Carrier65 provider or the larger
`StructuredEndpointMF` client.

Attempt01 **failed** at Lean's `-M2400` interpreter memory limit,
exit −6, before producing an object or theorem reports. It ran 1.977
seconds with peak sampled RSS 2,543,140,864 bytes; guards remained stable
and the monitor did not stop the process. This is a resource failure,
not evidence for or against the draft conclusion. The two constituent results remain individually checked:
`../rational-carrier64-current14-actual-external/` and
`DiophantineConsistency.IPRAStandardCurrentEndpoint.ipra_current_iff_consistency`.

Attempt02 changed only Lean's interpreter limit to `-M2800`, retaining the
120-second timeout, sampled 3.5 GiB group-RSS stop, 10 GiB available-memory
floor, nice 19 and idle I/O. It **passed**, Lean and runner exit 0, with
no warnings or `sorryAx` and axiom report `[propext, Classical.choice,
Quot.sound]`. The run took 2.714 seconds, peak sampled RSS was
2,844,966,912 bytes and minimum available memory was 18,819,403,776 bytes;
the guards were stable. The output object is
`/tmp/rational-carrier64-current14-pair-priority-check02/RationalCarrier64CurrentPair.olean`,
SHA-256 `da0337c6058b21c5ae5b31eed1fa4e3d69cfe3c02eb2fce469b5bae384fd4dc3`.
Transitive/dynamic ancestry and sampled resource monitoring remain
limitations. This paired theorem is a conjunction of an **external**
ordinary rational/integer statement and a derivability statement about
the existing integer syntax. It is not an iPRA derivation of an equation
containing rational constants.

The outer runner session 52835 was separately observed to exit 0; the
retained `observations/attempt02/outer-terminal.json` records that tool
observation independently of the child's result receipt.

| Artifact | SHA-256 |
| --- | --- |
| `RationalCarrier64CurrentPair.lean` | `92cde64344af599049f535a6237dfeeb134e44bdc3c6506bc2c07ae1759ba35e` |
| `check01.py` | `b82cbcf3ceeb4d45b0e87cf3e51195eb7449571403f5ea3ff58086cd47ecfa52` |
| `observations/attempt01/compile.log` | `48bc2200174632932b9ea98fd0a0c30e6dc353ce535531045f1c7efc7b79940a` |
| `observations/attempt01/result.json` | `888546ce099bf81340bca14140ecb1ba66a16b490b8a0922ba0fa3002557cb79` |
| `check02.py` | `b43bf7a70fd8d40219718cb241f84404f1ca389f70e5d7e879895190992b91af` |
| `observations/attempt02/compile.log` | `f37e120a0a57ab4ddbd4a1299dbb2d1137fafcba6b594e551771692bb34fdda0` |
| `observations/attempt02/result.json` | `0e3cccd62ef35352f9ccbe00639947f580ec5b1a2adeb05561a58a263a945593` |
| `observations/attempt02/outer-terminal.json` | `eb8c6ff96a7c66a5f74ae079c59e0d77960a804fc36540cf673a3894a3aa3e2f` |
