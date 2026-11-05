# Attempted once-beta-shift identity for current2011 MF

This is a **failed diagnostic**, not a Lean proof of the shifted port. The
source imports the [successful isolated high-mask recipe identities](../current2011-mf-recipe-diagnostic/README.md)
and the separately checked current-base `Current14LiteralPortsMF` provider.
It defines a natural high mask plus beta, then attempts to identify its integer
cast with `CurrentWindowCarry2011.ports 3` using the existing port projection.

In [attempt 01](attempt01/) the kernel exhausted the configured memory limit
while checking the shift cast; observed outer session 85751 exited 1. In
[attempt 02](attempt02/) the natural-to-integer cast and substitution were
first factored into a parametric lemma, but kernel checking its specialization
`shiftedValue_cast` still exhausted the limit; outer session 69041 exited 1.
The self-dependent axiom reports in those logs are consequences of failed
declarations and are not theorem evidence. Both runs used Lean `-M2800`,
one thread and a 180-second foreground timeout; no memory cap was raised.

An [external finite check](../current2011-mf-byte-binding/README.md) separately
compares the once-shifted symbolic recipe to the recorded MF payloads. The
remaining Lean connection from that recipe to port 3 is not established here.
