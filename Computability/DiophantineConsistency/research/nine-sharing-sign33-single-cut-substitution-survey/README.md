# Single-cut substitution syntactic survey

This external, deterministic source-pinned survey examines each of the 19 materialized-cut definitions in the audited 33 residual AST. In each case it substitutes that cut's displayed right-hand side for the cut variable in all other displayed residuals, drops its defining residual, and computes syntax-tree degree without cancellation or algebraic rewriting. Fourteen positive and five signed cuts are included; signed substitution would require separate natural-representability arguments.

All 19 substitutions leave at least one displayed residual of syntactic degree 3 or 4, so none retains the current sum-of-squares form with all residuals syntactically quadratic. This does **not** prove actual degree greater than four for every case: syntax-tree bounds may overestimate degree after cancellation. It does not rule out a different quartic residual encoding, a different source representation, multiple interacting changes or a 32-witness quartic seed, and it establishes no global lower bound. The separately audited q²-elimination candidate has its own exact degree-six argument.

Author no-Lean execution exited 0. Checker SHA-256 `185bb574334e138a506881aacaadf91becefd97cd59c47519c3c2a9d9bb63b82`; result SHA-256 `6a8a398f49b61b4b09b562922d4e242276ce19e5b4b885caee0c0fb509286ab2`. Independent review required.

The [independent syntactic survey audit](../../reviews/nine-sharing-sign33-single-cut-survey-frontier-independent/) passed using a separate variable-weight recursion. It confirms 11 syntactic degree-three and eight degree-four residual maxima, with the same non-exhaustive semantic scope.
