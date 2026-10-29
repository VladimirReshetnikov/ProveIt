# Reverse adaptive strong-factor identity

`adaptive_strong_identity` proves `(delta*i*c*c)^2 = delta*(f*f-1)`
from the maintained strong norm. `adaptive_strong_of_equations` specializes
this to the actual 14-coordinate equation system with its literal radix,
rank-dependent coordinates and scaled multiplier `delta*i`. It supplies one
strong-factor identity for the reverse witness map; it does not construct
the full adaptive vector or prove its polynomial zero.

Two fresh root builds against the independently replayed reverse-transport
provider `/tmp/adaptive13-construction-transport-l43kh3xz/lib` passed with
identical source, object and complete-log hashes. Both axiom reports contain
`propext`, `Classical.choice`, and `Quot.sound`. The [drivers, snapshots,
logs, provider inventories and states](adaptive-construction-strong2011-replay/)
are preserved. Foundation/packages and inherited project objects remain cache
boundaries, not a fresh transitive source audit.

A subsequent upstream merge changed `ArithmeticCarrierRadix2011.lean`. This
receipt authenticates the earlier dependency snapshot; the affected
source-current downstream replay is pending.
