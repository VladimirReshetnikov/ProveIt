# Independent audit: same-source cleared-pair replay

**PASS for the recorded same-base replay.** The original and replay used
the same source bytes, command and ordered provider search path, with only
the output-object path changed. Their output objects and complete compiler/
axiom logs are byte-identical. Every one of the original run's 178 recorded
direct-input, companion and shadow guards appears unchanged in the replay;
the replay also records four additional pins for the original evidence.
All 182 replay guards matched at review time.

Both retained child results report Lean exit 0, no resource stop and stable
guards. Separate retained outer observations record original session 53951
and replay session 4597, both exit 0; this review did not observe those
sessions directly. The [independent checker](check.py) ran exit 0, comparing
source, full object/log bytes, commands, ordered paths, resource receipts,
outer observations and guards; its output is [result.json](result.json).
The replay output object hash is
`6f8afbccd823e06ce3173999dcedab7828abb573d04e7855fa40583298584cdb`.

This is a repeated client compilation against the **same captured current14
base and provider objects**. It is not an independent provider rebuild or a
transitive/dynamic ancestry audit; resource checks remain sampled. The
reviewed theorem remains a conjunction of an external rational zero iff
and an iPRA theorem for existing cleared integer syntax, not an internal
rational-leaf theorem or a 64-operation integer-leaf equation. The original
[client review](../rational-carrier64-cleared-pair-independent/README.md)
records its exact statement.

Checker SHA-256
`ba4df5ab1d1f1111046d79eb5b393d7e579ae1e1066857069fb021698265dc81`;
result SHA-256
`e9041b127132887e6f5809b9f302546af365d3ecc1161bb5f21ffcfd82eddd56`.
