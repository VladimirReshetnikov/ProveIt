# Source and claim ledger

Access date: 26 November 2026. Repository data retrieved through the GitHub connector, public literature through web search.

## Pinned primary repository

`lsernau/grh-lean`, commit `72fead102f663d5c7a407964a13dc0cf9d977207` (commit message: Lean proof of GRH; 25 Nov 2026, 20:38:07 UTC).

Base: https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207

Inspected files and roles:

- `README.md` — scope, build prerequisites, reported machine checks and human-review limitation; blob `fdca72cbfa3557506543b662317267897e0058a0` (retrieved on main).
- `grh/GUIDE.md` — reading order, short/enough/long forms, height comparison, prime remainders; blob `c2acf9584b58efcb39ac1d668d25c107c3e76a0b`.
- `grh-compact/README.md` — five statements, Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`, Lean v4.35.0, reported kernel and Comparator checks.
- `grh-compact/Challenge.lean` — statement-only Comparator challenge, not imported by the built proof. Its `sorry`s are intentionally in that challenge; they are not evidence of `sorry` in `src/Main.lean`.
- `grh-compact/src/Statements.lean` — definitions of four headline propositions in addition to Mathlib's RH.
- `grh-compact/src/Main.lean` — wrappers deducing five headline theorems from `New.grh` and the functional-equation lemmas.
- `grh-compact/src/New/Main.lean` (lines 1–160) — `star_inequality`, `eventually_primeError_le_rpow`, cancellation of the common height in upper/lower estimates, one-sided endgame.
- `grh-compact/src/New/Endgame/OneSidedCriterion.lean` (lines 1–85) — weighted nonsplit prime remainder, quadratic twist selection and Landau analytic criterion.
- `grh/src/New/Reduction/OneSidedBound.lean` (lines 1–100) — readable ramp definition and comparison at two scales.

## Public sources

- https://en.wikipedia.org/wiki/Riemann_hypothesis — classical RH consequences, explicit prime error, Dirichlet vs. more general GRH.
- https://www.math.uwaterloo.ca/~mrubinst/alpoge_claude_grh/ — independent checks of the original formalization; explanatory work remains a separate matter.
- https://doi.org/10.1090/mcom/3599 — Bennett, Martin, O'Bryant, Rechnitzer, Dirichlet zero counts (2021).
- https://arxiv.org/html/2411.07436v3 and https://doi.org/10.1007/s11139-025-01238-9 — Suzuki, sign criteria for weighted prime sums (2025), including central zero terms. Closely related but not evidence that the two-step finite binomial filter or its uniform rate is already known.
- https://research-information.bris.ac.uk/ws/files/67056122/PsiTilde_12_2.pdf — Platt and Ramaré, centered Lambda(n)/n sums in arithmetic progressions (preprint date 2015-03-05).
- Montgomery & Vaughan, Multiplicative Number Theory I (2007); Davenport, Multiplicative Number Theory (3rd ed., 2000) — classical analytic tools (Hadamard products, zero counts, explicit formula and Landau principle).

## Dependency boundary

The original contribution is the fixed two-scale filter, its quantitative attenuation, the constant-eliminating difference, and their joint forward/converse theorem. The underlying Mellin transform, one-sided Landau argument, and Dirichlet zero counts are classical. The result is stated as a consequence of the repository's Dirichlet GRH theorem, not a proof of its high-rank automorphic machinery and not a claim that any other previously open conjecture has been settled. Literature searches were targeted rather than exhaustive; publication priority remains open.
