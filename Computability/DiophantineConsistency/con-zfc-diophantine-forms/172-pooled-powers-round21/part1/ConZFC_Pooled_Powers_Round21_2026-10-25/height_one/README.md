# Round21: unit-homogenized height-one quartics

| Endpoint | Variables | Collected monomials | Round20 monomials |
|---|---:|---:|---:|
| minimum503 | 503 | 24,183 | 24,193 |
| compact505 | 505 | 20,405 | 20,491 |
| compact512 | 512 | 18,184 | 18,255 |
| balanced557 | 557 | 11,991 | 11,999 |
| sparse617 | 617 | 8,314 | 8,318 |
| sparser713 | 713 | 7,172 | 7,176 |

Every literal polynomial is real-nonnegative, exact degree four, has constant one and collected nonzero coefficients exactly ±1. All variables are unrestricted integers. Through the pinned inherited source calibration, ordinary ZFC proves that integer unsolvability is equivalent to Con(ZFC). This is not a consistency proof or an optimality claim.

The first new operation replaces a two-alias equality penalty by C(f1,f2,f3), where every fi is a class alias, optionally multiplied by an already anchored unit, and both aliases occur. Twice C is the sum of the three cyclic square differences. Units equal one at every zero, so the new penalty has the identical equality zero set, without new coordinates. Exact global coefficient checking selects strict support reductions. `PROOF.md` gives the complete proof, source lift, inverse, and essential hub-square identity. All six Round20 selected endpoints are strictly dominated in monomial count, at unchanged variable count. The compact505 and compact512 profiles also split c*x*y into signed products (a*x)*(b*y), a*b=|c|, reusing triangular monic scales. Both mechanisms are structural, not seed-only selections.

## Reproduce and audit

Python 3.10+ and the standard library only:

    python verify.py --report REPLAY_BOTH.json

The default runs normal and optimized Python. It independently reconstructs every coefficient from literal squared divergences and equality/unit squares, verifies source pullbacks, occurrence ledgers, trees and universal symbolic lifts, parses every literal equation, rejects 21 final-artifact mutation classes per endpoint, and rebuilds all source transformations and final bytes. Step audits check old dummy/flow transformations and the new exact penalty-difference identity with eight or eleven step mutation classes. Matched Round20 input hashes and both intermediate cycle-only compact controls are checked during replay, with identical sources, hubs and seeds. `--single` uses the current interpreter; `--skip-rebuild` omits producer reruns and step replay. `build.py` regenerates selected files.

`endpoints/*/polynomial.json` is the complete coefficient array; repeated zero-based indices encode powers. `polynomial.txt` is the identical explicit equation in ordinary one-based notation. Final certificates contain only semantic source/alias/graph/equality data. Intermediate ledgers are generated during replay rather than retained with stale namespaces. `SOURCE_BINDINGS.json` identifies the enclosing inherited proof interfaces. `RELEASE_WHITELIST.json` is the sole release allowlist: trial sources, negative searches and experimental files are excluded.

Source count reductions in this round's separate signed branch do not automatically improve these height-one equations. Tested pooled source transfers were not selected; the height-one endpoints retain the explicitly pinned Round20 source closure.
