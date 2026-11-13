# Conditional Q-unit norm check

Source-only and uncompiled. The candidate maps the explicitly assumed core Q=1 under arbitrary model ports and the same shifted input tuple to the constructor Q field; all five signed representatives remain arbitrary. Source-zero, other fields, concrete port casts, full seed bridge and endpoint remain separate. Proof elaboration, resource fit and provider compatibility remain untested; independent prelaunch review is required.

The check source differs from the retained draft only by an explicit `Fin 34 → V` valuation annotation, based on a separately observed `Fin.cons` inference failure. Author no-Lean preflight session 47220 exited 0. Pins: source `faffcb8c15c734a4e2747196d1e1e3ae2587633b0ed1bc0cb67065c3d8b42f92`, manifest `058c68b9c700afbfede003943a3c5267565e17166f5602be44d886366144125b`, survey `e93e0ae60790a3d94e7fa5dcc43319e962df44972ad865e7989b00f738809f25`, runner `5423ea29e2da24360d3530c01872cdf7b26833cb3e244bfe5dd7773ea9d613a0`. Preflight is point-in-time source/provider evidence; it does not establish elaboration or a complete transitive dependency trace.

The reviewed Lean run failed in author-observed outer session 7961, exit 1. The compile log reports a Lean interpreter memory exception; no Q-norm theorem was produced. See `attempt01/`.

Independent failure audit: [`reviews/nine-sharing-sign33-forward-norm-q-failure-frontier-independent/`](../../reviews/nine-sharing-sign33-forward-norm-q-failure-frontier-independent/).
