# Independent second-order A202061 audit

The two independent proof audits establish

D_n = C n^(1/3)(log n)^(2/3)
      + (7C/3)n^(1/3)(log n)^(-1/3)loglog n
      + O(n^(1/3)(log n)^(-1/3)),

where C=(3 pi^2 alpha^2/(2v))^(1/3).

- `lower-construction-audit.md`: exact-length coefficient lower bound, balanced good bridges, Jensen cancellation, global legality, and O(M) error accounting
- `upper-calibration-audit.md`: matching coefficient upper bound, uniform finite-n calibration, quantitative endpoint cost, transformed-row tails, and terminal factors
- `foundation-identities-replay.txt`: successful replay of the already-frozen independent algebraic identities

The lower construction's originally incorrect separate o(1) rounding assertions were corrected by its author to O(log n), which is harmless within the theorem's remainder. No other correction or unresolved gap was found in either main proof. All frozen reports were left unchanged. No coefficient amplitude or constant at the next F/log n order is established by this audit.

Separate auxiliary result, audited afterward:

- `finite-height-constant-audit.md` certifies log(rho_H/rho)=alpha/H[(1/2)log H+loglog H+c_*+o(1)], with c_*=0.8667962458055399529886348076493373710016...
- `check_finite_height_amplitude.py` and `finite-height-amplitude-output.txt` independently certify the previously unaudited fixed-q amplitude

The auxiliary finite-height constant is not asserted to equal the global deficit's next undetermined constant.
