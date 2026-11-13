# Sign24 bridge via sign26: source-only alternative

This candidate composes the checked sign24↔sign25 and sign25↔sign26
model-zero equivalences and transports the checked sign26 polynomial bridge
directly. It avoids importing the concrete sign25 polynomial-bridge theorem;
the sign25 expression-equivalence provider and sign26 bridge provider still
need a byte-compatible union with the sign24 base. Compared with the failed
sign24 attempt, this changes the import and elaboration route under the same
limits; it does not guarantee a memory reduction.

A matching source copy failed with an interpreter memory exception in a
guarded run under the same limits; the [independent failure audit](../../reviews/nine-sharing-sign24-polynomial-bridge-bypass-terminal-independent/README.md)
records that result. The draft does not establish an iPRA endpoint, Lean
degree theorem or external-byte binding.
