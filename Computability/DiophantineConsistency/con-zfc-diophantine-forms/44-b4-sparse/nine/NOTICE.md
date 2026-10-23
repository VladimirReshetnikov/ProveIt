# Attribution and dependencies

This construction is derived from Vladimir Reshetnikov's ProveIt report series, reviewed at commit 22e75dd6b87b1b199bb08c778d7cf075ae5aae08. The inherited Jones ratio/central-binomial bridge, the 31-witness quartic, literal K215 calibration, 943-tile compiler, and completed-square/finalizer work retain their original attribution. Relevant source reports include 30-quartic31, 31-sun10, 34-integer14, and 37-wave5.

The B4 digit placement and sparse fixed-polynomial two-carry proof are joint contributions of the companion package. The present nine-variable lane adds unconditional positivity from the fixed source's positive constant term; the exact DF near-square majorant S0=iJC(8D²−4D−1); its 64-fold square scaling; a positive-divisor finalizer; and the corresponding exact degree/circuit artifacts. It does not claim a new universal nine-variable theorem.

The arithmetic DAG and sparse homogeneous Horner evaluator adapt the report-series implementations and the companion Sun-B4 lane. All binary arithmetic is counted. Ordinary mathematical dependencies are identified in NINE_B4_PROOF.md and SOURCE_PINS.json. Finite validation is not formalization of those dependencies.
