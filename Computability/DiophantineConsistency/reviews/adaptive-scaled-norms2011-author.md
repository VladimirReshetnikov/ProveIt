# Adaptive scaled norms: author result

The new Lean pair derives the actual first and main scaled Pell equalities
from the literal 13-variable adaptive split zero in arbitrary IΣ₁ models.
The roots are magnitudes of the exact signed syntax subexpressions, not
assumed positive roots. The nonnegative right-hand sides are explicitly
identified as `M*M*(1+ell*(ell+k))` and `U*U*(1+delta*c*c)` with the
literal adaptive q, M, U, ell, k, c and delta. The current-port client and
single-shift natural client use the actual complete fixed ports.

The package also proves q>1 and positivity of M, U, k, ell for positive
coordinates and a positive first port, and discharges that port's positivity
for the actual current tuple. No quotient, divisibility or unscaled Pell
solution is assumed or concluded. In particular the separate theorem needed
to infer M∣|Z| from M²∣|Z|² is not part of this packet.

Two final fresh builds match both objects, both complete logs and all thirteen
axiom reports, which use only `propext`, `Classical.choice`, and `Quot.sound`.
Both builds were by the same author and require independent review. The
parent was the independently accepted factor-units provider; the explicit
package/toolchain interiors remain inherited boundaries. Each run rehashed
408 selected provider entries before and after compilation.

The [85-file evidence manifest](adaptive-scaled-norms2011-build-evidence/FILES.json)
SHA256 is `bd0a2099ad3bce7c71cbb0a1cc3465ee5f7737d1c50c02d93d8c15a339228b01`.
It preserves ten attempts, complete source snapshots, logs, timings and
drivers. Earlier attempts include a syntax-simplification error, a failed
right-hand-side reduction, and kernel exhaustion at 6 GiB when a fixed-port
cast proof expanded large constants; the successful repair proves the cast
for arbitrary four natural ports before specializing. The final successful
provider is `/tmp/adaptive13-scaled-norms-j7_n8ujg/lib`.

| Source | Source SHA256 | Object SHA256 |
| --- | --- | --- |
| ArithmeticAdaptiveScaledNorms2011 | `b614f5a208973fa9b286271fe047c66ad30ed3dbd30d22d44e734c97a55438ec` | `0eeab89040c678c8e7cc8dcd008fc3ec304e81a8ae5a08f080762b7a61a44fd5` |
| ArithmeticAdaptiveScaledNorms2011Checks | `1c1cfcf35b46009569def410564bd831f36300f9292c6bf11c891a8a53b65e5e` | `cd65f7c0ef42c7da82bb3ab445e5d17cbd66d0ab93f3dcb61cffb8b74430e56c` |
