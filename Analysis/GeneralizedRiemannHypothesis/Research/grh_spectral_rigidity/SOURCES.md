# Source audit (2026-11-26)

Repository: https://github.com/lsernau/grh-lean
Default branch: `main`. Retrieved recursive tree SHA: `72fead102f663d5c7a407964a13dc0cf9d977207` (tree identifier, not asserted to be a commit ID).

Files actually fetched through the GitHub connector, with reported blob identifiers:

| File | Blob SHA | Scope |
|---|---|---|
| [README.md](https://github.com/lsernau/grh-lean/blob/main/README.md) | fdca72cbfa3557506543b662317267897e0058a0 | entire |
| [grh-compact/GUIDE.md](https://github.com/lsernau/grh-lean/blob/main/grh-compact/GUIDE.md) | ca70306f0ee22fca325f7f515667e51625e8eabd | entire |
| [grh-compact/README.md](https://github.com/lsernau/grh-lean/blob/main/grh-compact/README.md) | 85d43d83a7fa3b496968ce9216f4a7d75e44e84a | entire |
| [grh-compact/Challenge.lean](https://github.com/lsernau/grh-lean/blob/main/grh-compact/Challenge.lean) | 4230ff8fe8b0265a44db348c22cd5f03a7c3f3fe | entire |
| [grh-compact/scripts/PrintAxioms.lean](https://github.com/lsernau/grh-lean/blob/main/grh-compact/scripts/PrintAxioms.lean) | ec5adcfd7baeff36130db9a763720ba1a6567c57 | entire |
| [grh-compact/src/Statements.lean](https://github.com/lsernau/grh-lean/blob/main/grh-compact/src/Statements.lean) | 1cd1bce93344065936b2b392b23306254e0785ef | entire |
| [grh-compact/src/Main.lean](https://github.com/lsernau/grh-lean/blob/main/grh-compact/src/Main.lean) | a5d8389131c985a0b54ce5b0e778ee5c8126a997 | entire |
| [grh-compact/src/New/Main.lean](https://github.com/lsernau/grh-lean/blob/main/grh-compact/src/New/Main.lean) | 198ed5bf26aa294898931e0649bc2b88f1389f65 | lines 1–160 |

The top-level `LFunction_ne_zero_of_half_lt_re` and `LFunction_eq_zero_re` provide exactly the Dirichlet GRH input. `Challenge.lean` contains `sorry` by design: it is a statement-only Comparator challenge, not imported by the main proof. The README reports that the main proof is free of `sorry` and that the usual three axioms are the only dependencies. This note does not reproduce that build.

Public sources consulted:
- https://en.wikipedia.org/wiki/Riemann_hypothesis — formulation, consequences for prime distribution, analytic criteria, related correlation questions.
- https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/ — reported independent verification of the original proof; human-readable account remains in progress.
- https://andrewodesky.com/rh/overview.html?v=32 — overview of primitive character reduction and analytic endgame.
- https://arxiv.org/abs/2607.22930 — Banks–Loftus, unshared zeros (abstract).
- https://arxiv.org/abs/1710.00088 — Martin–Ng, inclusive prime number races (abstract).

Classical inputs are standard results in Davenport and Iwaniec–Kowalski, cited in the manuscript. Targeted searching is not exhaustive; bibliographic novelty is unverified. The new mathematical argument is independent of the internal covolume proof, except that its GRH-dependent conclusions use the headline theorem as input.
