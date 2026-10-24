# Power-fused global tiling certificates

A proved arithmetic advance on the alternative, non-Jones certificate route. The geometry no longer requires two indexed powers, and the binomial-free interface no longer requires five power calls.

## Results

| Exact natural interface | Exposed coordinates | Special graphs | Conditional ordinary-polynomial count |
|---|---:|---|---:|
| One-power/binomial | 5 | 1 fixed-base-2, 1 total-binomial | 5+p2+b |
| Three-power | 7 | 2 fixed-base-2, 1 general-base | 7+2p2+pg |
| Two-power | 8 | 1 fixed-base-2, 1 general-base | 8+p2+pg |

Here p2, pg and b count **all** internal natural witnesses of literal exact graph polynomials, which remain uncompiled. These are not five-, seven- or eight-variable ordinary-polynomial results. Theorems apply to any finite strict-boundary tile set and to arbitrary rectangular tilings, not only square tilings or one chosen machine.

The new ingredients are:

1. A free top base-R digit simultaneously bootstraps the packed selector and previously unbounded width code.
2. The boundary identities themselves force the width to divide the area code and recover both geometric exponents.
3. A parity-extraction power supplies the geometry's power-of-two certificate by divisibility.
4. A second-order congruence synchronizes two powers exactly, with an explicit size bound and full natural witness map.

See PROOF.md for the universal proofs, exact ordinary-polynomial contracts, degree bounds and limitations. SOURCES.md records primary background and predecessor provenance.

## Reproduce

    python check.py
    python -O check.py
    python build_dag.py
    python build_interfaces.py

Only the Python standard library is needed. Normal and optimized tests must both pass. The checker deliberately includes invalid, oversized width codes and malformed packed selectors. Tests are not a proof assistant formalization.

The three JSON artifacts contain only fixed nonnegative integer powers in their ordinary-polynomial expression DAGs. Uncompiled variable-power graphs are declared separately, never disguised as polynomial operations. FOUR_TILE_DAG.json evaluates the packed circuit; THREE_POWERS_INTERFACE.json and TWO_POWERS_INTERFACE.json include every exposed port and ordinary residual.

A literal direct ZFC-checker tile set, actual exponent/binomial graph polynomials, and complete internal ZFC interpretation remain required to produce the requested alternative ordinary consistency polynomial. The existing generic TM compiler can be reused, but is not supplied as an independent ZFC checker here.
