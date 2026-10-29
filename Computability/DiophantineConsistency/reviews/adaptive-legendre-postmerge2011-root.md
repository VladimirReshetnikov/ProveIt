# Intermediate replay after the Legendre refactor

An independent replay compiled all 18 modules from snapshots taken after the
Legendre change and matched the author source, object and complete-log hashes.
The updated Legendre source itself was independently rebuilt, with the existing
unnecessary-simpa warning at line 78 retained. The replay then marked its state
`FAILED` during final source reauthentication: an upstream merge changed
`ArithmeticHalfBinomial.lean` after the snapshots were taken. This is therefore
evidence for the frozen post-Legendre/pre-HalfBinomial snapshot, not a
source-current acceptance of the downstream chain.

The [independent driver, snapshots, logs, provider inventory and failed state](adaptive-legendre-postmerge2011-root-replay/)
and [author receipt](adaptive-legendre-postmerge2011-author.md) are preserved.
The driver inherited the independently replayed post-CarrierRadix window
provider; Foundation, packages and unchanged project objects remain cache
boundaries. A fresh HalfBinomial-to-client replay is required.
