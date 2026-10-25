# Round19: polarized height-one quartics

| Endpoint | Variables | Monomials |
|---|---:|---:|
| minimum528 | 528 | 20,816 |
| compact534 | 534 | 18,543 |
| balanced580 | 580 | 12,001 |
| sparse620 | 620 | 8,318 |
| sparser717 | 717 | 7,176 |

Every polynomial is nonnegative over the reals, has exact degree 4 and constant 1, and has every nonzero collected coefficient ±1. All variables are unrestricted integers. Ordinary ZFC proves that its integer unsolvability is equivalent to Con(ZFC), using the explicitly bound inherited source calibration. This is not a consistency proof or global-optimality claim.

The new structural step replaces prescribed square labels by products of same-logical aliases. This permits a quartic two-alias equality penalty and deletes an otherwise necessary equality dummy. The two smallest endpoints also transfer the new 247-variable signed source through a fixed certified affine refactorization. `PROOF.md` proves both witness directions, uniqueness, and the universal off-zero lift identity.

Run with Python 3.10+ and the standard library only:

    python verify.py --report replay.json

This runs normal and optimized Python, independently checks every coefficient and symbolic lift, parses the literal equations, rejects 17 corruption classes per endpoint, and regenerates every source transformation and output byte-for-byte. `--single` checks just the current interpreter; `--skip-rebuild` omits producer reruns. `build.py` regenerates the selected artifacts.

The four matched-source comparisons isolate polarization alone, retaining the prior source, hubs and seed: 571/19,833 → 559/19,809; 593/12,027 → 580/12,001; 646/8,368 → 620/8,318; 742/7,226 → 717/7,176. Baseline polynomial and certificate hashes are verified against the exact prior artifacts. The 559-variable comparison is regenerated evidence, not a sixth released endpoint.

`endpoints/*/polynomial.json` contains the complete collected coefficients; repeated zero-based variable indices in a monomial encode powers. `polynomial.txt` is the same equation in ordinary one-based notation. `SOURCE_BINDINGS.json` names the enclosing proof interfaces. `RELEASE_WHITELIST.json` is the only release allowlist; trial folders and exploratory programs are not release material.
