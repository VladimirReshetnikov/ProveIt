# Round20: anchored-unit height-one quartics

| Endpoint | Variables | Collected monomials |
|---|---:|---:|
| minimum503 | 503 | 24,193 |
| compact505 | 505 | 20,491 |
| compact512 | 512 | 18,255 |
| balanced557 | 557 | 11,999 |
| sparse617 | 617 | 8,318 |
| sparser713 | 713 | 7,176 |

Each literal polynomial is nonnegative over the reals, has exact degree 4, constant 1, and nonzero coefficients exactly ±1. Every variable is an unrestricted integer. Ordinary ZFC proves that integer unsolvability is equivalent to Con(ZFC), through the explicitly pinned inherited source calibration. This is not a consistency proof or an optimality claim.

The new operation replaces a private equality dummy d in C(a,b,d) by a product a*u using an already anchored unit alias. C(a,b,a*u) is still a nonnegative quartic equality penalty and introduces no coordinate. Exact height checking removes all remaining equality dummies in these endpoints. A second operation contracts internal network tree edges and deletes their flow coordinates, with an explicit integral inverse. `PROOF.md` proves both directions, uniqueness and the universal off-zero lift including the hub square.

The smallest three outputs also use this round's exposed241 and power-exposed242 signed sources. The 503-variable equation is a variable-count tradeoff; the 505-variable equation has both fewer variables and fewer monomials than the prior 528/20,816 endpoint. All five prior selected endpoints have a strictly dominating released successor.

## Reproduce and audit

Python 3.10+ and the standard library only:

    python verify.py --report replay.json

The default runs both normal and optimized Python. It independently reconstructs every coefficient from literal squared divergences and equality/unit square identities; verifies all source pullbacks, occurrence ledgers, trees, exact symbolic lifts and collected metrics; parses each literal equation; rejects 16 final-artifact mutation classes per endpoint; and rebuilds every source transformation and final polynomial byte for byte. The independent step checker additionally verifies complete dummy substitutions, exact flow quotient graphs and the off-zero flow restoration identity, with four or seven step mutation controls per endpoint. `--single` selects the current interpreter; `--skip-rebuild` omits producer reruns and step replay. `build.py` regenerates selected files.

Five fixed matched-source comparisons isolate the structural operations, with exact prior polynomial/certificate hashes checked before transformation:

- 528/20,816 → 508/20,808 (flow, renewed alias contraction and anchored-unit equality).
- 534/18,543 → 518/18,543.
- 580/12,001 → 557/11,999.
- 620/8,318 → 617/8,318.
- 717/7,176 → 713/7,176.

The last four use anchored-unit equality alone. The 508- and 518-variable comparison outputs are reproducible evidence, not additional released endpoints.

`endpoints/*/polynomial.json` is the actual complete coefficient array; repeated zero-based indices encode powers. `polynomial.txt` is the identical equation in ordinary one-based notation. Final certificates contain only semantic source/alias/graph/equality data; intermediate transformation namespaces are generated during replay, not left stale in final certificates. `SOURCE_BINDINGS.json` names the enclosing proof interfaces. `RELEASE_WHITELIST.json` is the only release allowlist; exploratory files and trial outputs are excluded.
