# Sign23 polynomial bridge via sign24: source-only draft

This proposed client adapts the sign24 polynomial-bridge transport to the
Fin23 expression, using the audited sign23/sign24 model-zero equivalence and
the independently audited sign24 concrete bridge. That sign24 bridge was
checked under a scoped `-M3600` retry after failures at `-M2800`; its provider
union and memory qualifications must be retained. A matching source copy
passed a guarded `-M3600` build and [independent terminal audit](../../reviews/nine-sharing-sign23-concrete-polynomial-bridge-terminal-independent/README.md).
An iPRA endpoint, Lean degree theorem and external-byte binding remain separate.
