# Exact arithmetic of the canonical cyclic cell coordinate

Date: 2026-10-26. Independent full source/check review and fresh replay:
ROOT. See the [author receipt](current-cell-coordinate2011-author.md).

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| CurrentCellCoordinate2011.lean (147 lines) | 6e316a7a9a0107e8bc2bc41bf2bcd5868251b297f0b5cd7c79b64a52da1e9f48 |
| CurrentCellCoordinate2011Checks.lean (92 lines) | 4149684d1c8c344e8357ba3831c2627875cf55cdca1f37ec6566006dd73f30be |

ROOT read both complete final sources before fresh direct `lake env lean
-M6000 -j1` runs. Main output was written to a separate temporary object;
checks imported the frozen author-built main. Both passed, with empty
main diagnostics and seventeen standard-only axiom audits. Existing
prerequisite objects were reused; no entire dependency or umbrella
rebuild is claimed.

The coordinate equals the cast of b.val/2011, and its inverse has physical
base cast(j.val*2011). Equalities in the large word cancel the factor2011
from both representatives and modulus; there is no claim that2011 is a
unit moduloN. This proves exact plus/minus1 spatial transport, arbitrary
whole-cell subtraction and the inverse-coordinate identities.

The literal aligned subtype b-t has coordinate coordinate(b)-t/2011 when
t%2011=0. Its definition agrees with theta t; a separate interface permits
any alignment proof for the same physical base. Focused checks bind that
subtype to the independently defined actual previousCell and temporalCell,
including unrestricted W/47 and quotient(W/47)/2011. Adding complete
periods and N=1 are covered. Scaled nonzeroness transfers to the smaller
cycle without coprimality. These statements contain no word, Facts,
occupation, tiling or intended-equivalence premise.

This supplies coordinate transport for the actual marked-word adapter.
It does not itself prove existence of a tiling or any machine semantics.
The maintained decimal equation and its metrics are unchanged.
