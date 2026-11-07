# P norm tau-projection retry

Source-only and uncompiled. The sole source-proof change isolates the constructor tau-coordinate equality and then applies the original tau hypothesis without simplification of the core expression, addressing the retained map-add normalization mismatch. The theorem statement, assumptions, exact provider and resource caps remain unchanged. Source-zero, seed bridge and endpoint remain separate; independent review and Lean checking required.

Author no-Lean preflight session 16785 exited 0. Pins: source `53ca289ae6f0dc79b03cc5072bd3b45bcc57f561988afefe991209bf7f710c3f`, manifest `9f1f397903f1b1f773873387b64bfa4391b4ba1298a04dc6ca55c9fa3860d073`, survey `2c3c9a64d8778dfbda7a55663e4ff73179e4d042e9caa0238b5bda3124fbf99d`, runner `52b4371c30212c72766e3f7dec1c7f313d3dbc0d24230d8dfda08477d648e48e`. Preflight is point-in-time evidence only; Lean elaboration and full transitive tracing remain outside scope.

The reviewed run succeeded in author-observed outer session 87401, exit 0; see `attempt01/`. The P and tau hypotheses remain explicit.

Independent terminal audit: [`reviews/nine-sharing-sign33-forward-norm-p-retry02-terminal-frontier-independent/`](../../reviews/nine-sharing-sign33-forward-norm-p-retry02-terminal-frontier-independent/).
