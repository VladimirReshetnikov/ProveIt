# Fin14 compact prefix formula candidate

These five ASCII files encode the residual ASTs from the pinned external
sign14 seed. Prefix operators `+`, `-`, `*` are binary; `a` through `o` are
coordinates 0–14, `B`, `K`, `C`, `F` are ports beta, K0, MC, MF, and digits
1–4 are integer constants. The equation is the sum of the five squared
residuals equal to zero, with coordinate 0 fixed to one and coordinates 1–14
ranging over natural numbers. The [checker](check.py) decodes all five files
and compares their trees and byte hashes with the pinned seed JSON; the author
run exited 0. This is a reproducible external check, not a Lean theorem. The
[source-only Lean binding draft](../nine-sharing-sign14-prefix-binding-draft/README.md)
proposes kernel-checking the embedded prefix bytes against the symbolic staged
rows. Fixed port byte values and the existing equation PDF remain separate.

The [independent external audit](../../reviews/nine-sharing-sign14-prefix-formula-independent/README.md) passed; the packet is frozen.
