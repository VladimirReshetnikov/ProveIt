# New contraction certificates

## Proven relative results

- `frontier.tex`: full proofs for generic polynomial-space coefficient 63.7573555464258 (<64), and root-degree <=s^(1/12) coefficient23.6661688071455 (<24). Includes exact rational schedules, noncircular recursion bootstrap, growing-packet-degree analysis, precision/bit-cost audit, and stronger retuned two-stage comparison66.1204754600.
- `verify_multistage.py`: independently written standard-library checker for schedule capacity inequalities and rational coefficient upper bounds. All requirements use explicit exceptions (not assertions). Four exact negative controls test bad root capacities and impossible target constants. Normal and optimized replays agree in `replay_normal.json` and `replay_optimized.json`.
- `multistage_checks.json`: full exact certificates and per-level contributions.
- `cache_tradeoff/proof.md`: separately derived cached / three-block Strassen time-space certificates. Generic time37.9301090828846 (<38), space33.6230409216578 (<34); low-degree time14.2391881944397 (<14.3), space12.3613014575939 (<12.4). These are NOT polynomial-space algorithms.
- `cache_tradeoff/check_certificate.py`, `cache_tradeoff/check_lowdegree.py`: exact rational rounded bounds for the two cached schedules.

The code here was written for this task and does not execute any imported proposal code. No installation or upstream repository mutation was used. Numerical exploration in `explore_schedule.py`, `explore_lowdegree.py`, and `cache_tradeoff/search.py` was only for choosing candidates; it is not a global optimality certificate or part of the all-size proof.

## Imported mechanisms, not claimed new

The incoming asymmetric report supplies the two-stage exact-rational pair-load balancing, recursive side-degree invariant, and additive precision guard. The incoming joint Cauchy report supplies the all-level slope-four integral factorization, weighted pair entropy, group caches, and division-free Strassen method. The previously reviewed source supplies the deformation, interpolation/recovery, tensor children, and immutable creation-precision convention. The new contribution is the combined and depth-varying schedules, degree-growth accounting, and rigorously checked coefficients—not rediscovery of those mechanisms.

All statements are relative to those unchanged identities and the normalized contraction interface. They do not independently verify the ETH claim, establish a smaller logarithmic order, give measured solver runtimes, or place these coefficients directly before the SAT variable count n. General-density and low-degree hypotheses must not be conflated.
