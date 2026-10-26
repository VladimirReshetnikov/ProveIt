# Round22: shared monic factor-network height-one quartics

| Endpoint | Variables | Collected monomials |
|---|---:|---:|
| minimum493 | 493 | 24,828 |
| compact494 | 494 | 24,648 |
| compact496 | 496 | 20,548 |
| compact504 | 504 | 18,297 |
| compact507 | 507 | 17,524 |
| balanced546 | 546 | 12,139 |
| balanced557 (inherited) | 557 | 11,991 |
| sparse605 | 605 | 8,305 |
| sparser701 | 701 | 7,141 |

All equations are unrestricted-integer quartics, real-nonnegative, with
constant coefficient one and every collected nonzero coefficient ±1.
Through the exact pinned inherited source theorem, ordinary ZFC proves
integer unsolvability equivalent to Con(ZFC). This is not a consistency proof.

**New structure:** replace available composite constant definitions by
K_c−K_a*K_b, a*b=c; the minimum493 profile also shares existing scaled
variables via S(c,x)−K_d*S(c/d,x). Both are monic triangular constructors
with unique integer values. The final graph/lift proof and source equations
are unchanged. `PROOF.md` gives the full proof, source lift and inverse,
including the necessary hub-square term. Matched controls use identical
sources, hubs, seeds and coefficient splitting. Six controls are exact
frozen Round21 endpoint copies; h26 is explicitly a newly generated control.

The old 503/24183, 505/20405, 512/18184, 617/8314 and 713/7172 endpoints
are each dominated by a selected equation above. The old 557/11991 remains.
There is no claim of global minimality or an exhaustive Pareto frontier.

## Reproduce and verify

Python 3.10+; standard library only:

    python verify.py --report REPLAY_BOTH.json

Default verification runs normal and optimized Python, independently
reconstructs every coefficient from square differences, checks source and
constructor pullbacks, complete graph/alias semantics, symbolic lifts,
metrics and literal equations, rejects mutation classes, and rebuilds
selected polynomial/certificate/literal bytes plus matched controls.
`--single` uses the current interpreter; `--skip-rebuild` skips producer and
intermediate-step replay but retains final reconstruction and normalization
rewrite checks. `build.py` regenerates selected endpoints.

`endpoints/*/polynomial.json` contains every literal coefficient; repeated
zero-based indices encode powers. `polynomial.txt` is the identical explicit
equation using one-based variable names. `CONFIG.json` fixes all construction
parameters, control hashes and provenance. `SOURCE_BINDINGS.json` pins the
inherited original sources. `RELEASE_WHITELIST.json` alone defines the release;
exploratory code, source transfers and negative searches are excluded.

The new round22 signed-source candidates do not automatically improve this
height-one branch. Direct transfer tests were dominated and are not selected.
