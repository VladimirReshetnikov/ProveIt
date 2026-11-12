# Independent source review: literal 74 first factor client

The first-factor source rows give `X=q*w`, `Y=q³*s`,
`ell=(X*Y)*(Y*k)` and `F0=r²−ell*(ell+k)`. With the explicit beta cast,
the proposed ring cut is the exact identity `ell=(X*Y*Y)*k`; all other
ports are irrelevant to that field. The size argument uses positive beta and
J to give q≥2, positive w to give X≥2, and positive s and q to give Y≥1;
therefore m=X*Y²≥2. Its use of `pos_iff_one_le` supplies the needed model
arithmetic discreteness rather than relying on dense-ring inference.

The `five_positive_of_first_eval` application passes the same valuation,
first evaluation, m bound, product equivalence, and three residue exclusions
in the stated order. The generic pair-evaluation bridge is an explicit
**unreviewed dependency in this review**, not a result independently
validated here. Neither product equivalence nor residue exclusions are
claimed from a graph zero in this client.

The checker pins source bytes and relevant first-factor candidate rows, tests
4,096 positive size assignments and 2,000 signed ring identities, and
reproduces the author receipt. From `Computability/DiophantineConsistency`
run `python3 -I -S -B reviews/ordinary14-74-first-factor-client-independent/check.py | cmp - reviews/ordinary14-74-first-factor-client-independent/observation.json`.
Source and finite controls do not establish Lean elaboration, bridge/provider
compatibility, model or iPRA endpoint, or physical-byte/PDF binding. No Lean
run was performed.
