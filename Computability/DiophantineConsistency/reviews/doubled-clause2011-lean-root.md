# Full34-bit doubled-clause arithmetic

Date: 2026-10-26. Author: controller_certificate. Independent whole-source
and check review and fresh replay: ROOT. See the [author receipt](doubled-clause2011-lean-author.md).

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| DoubledClause2011.lean | 1285bb4332ad2dfabaee2a99eb1c7624d9a4c7c10e82dc3f25a2e6af92e6733f |
| DoubledClause2011Checks.lean | 01fafb8761d189147485c660b1bb38fa6751d73f411113e2c16021fa7fe1ff18 |

ROOT read all166 module and54 check lines before execution. Both fresh
direct `lake env lean -M6000 -j1` runs exited0. The main log was empty;
all eight axiom reports use only standard axioms. The author also freshly
checked the packet. Imported prerequisites were reused; no complete
ancestor or umbrella rebuild is claimed.

For every natural x, the full mask test is exactly x%2^45<=3. The actual
raw clause is2*n+2048*((2^34−u)*n+W)+k+t+b, reduced modulo2^47. From
n<=1, unsigned34-bit W,u, carry<=57 and Boolean t,b, the raw value is
already below the radix. Its outgoing carry is therefore derived zero
before using the mask.

Passing the mask gives exactly the empty case n=0,W=0,k+t+b<=3 or the
occupied case n=1,W=u,k+t+b<=1. Both converses are proved. Incoming
carry and temporal bit remain present throughout; focused checks accept
either one's permitted occupied contribution, reject a second low unit
and reject mismatched copied/selected words.

This is generic natural-number arithmetic. Binding W,u and the raw
expression to the actual physical clause requires the separate cell-label
module; no tile, occupation, alignment or consistency premise is used here.
