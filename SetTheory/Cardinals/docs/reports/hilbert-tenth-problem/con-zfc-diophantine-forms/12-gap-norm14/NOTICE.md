# Attribution and scope

This research contribution was prepared for Vladimir Reshetnikov's ProveIt
repository by an AI-assisted research collaboration on 22 October 2026.
It synthesizes the eight fixed-instance reports in
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms`
at commit `3b201cdea32d2c816f5f3d20734051f25fd3ef14`.

The principal inherited components are the raw blank-input K215 tableau
language (package 06), ordinary strong Pell norm (package 02), root elimination
(packages 03 and 05), quadratic lifting (package 08), and the native-window,
half-binomial, and inverse-population compiler proofs. The manuscript
identifies the additional algebraic and local-language simplifications.

The source files in `upstream/`, the three support modules in `compiler/`,
the literal `compiler/k215.tm`, and `arithmetic/baseline67.json` retain their
original contents. Their original repository paths and blob identities are
recorded in `provenance.json`. Relative links inside retained upstream notes
refer to their original repository locations and may require that context.
Historical verification claims in those notes are claims of their source
packages, not new runs by this contribution.

The original K215 notice is retained in `upstream/K215_NOTICE.md`. It credits,
within the stated scopes, Mira and ProveIt, Elliot Glazer, Jeff's busy-beaver
reference, Andrew James Wade, BusyCoq, and the Coq Library of Undecidability.
This archive contains only the copied components listed in its provenance;
it does not redistribute complete Lean/Rocq libraries. New contribution
material uses the project's MIT No Attribution terms in `LICENSE`.
`licenses/LICENSE.Wade` preserves the inherited compiler ancestry notice.

Reviews by separate agents are internal checks within this collaboration,
not external human endorsement. No global minimality, priority, new
kernel-checked Diophantine theorem, or unconditional consistency result is
asserted. The mathematical theorem and the scope of finite reproduction
checks are stated separately in the article.
