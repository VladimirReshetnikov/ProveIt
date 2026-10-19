# Independent review: reparameterized universal axiom rows

Date: 2026-10-18. Artifacts: `../logical_routes/permuted_rows`.
Table SHA-256: `fa866a802fc61cda9aae388750a0253088086470e0f86b5167cdcb4168a2b70e`.

## Verdict

The logical proof boundary is sound: each changed row emits exactly the same
set of numerical axiom instances as before. The new compiler must choose the
inverse parameter assignment when selecting an axiom leaf; it cannot reuse
old equal-parameter leaf statements literally. Bundle/gates and the independent
GEN entry remain unchanged. No new logical calibration is required beyond this
finite source transformation. The reported 267-state table remains above the
requested threshold and is not a certified binary consistency endpoint.

## Exact parameter coverage

Numbering in the artifacts is push order, the reverse of rho1..rho8:

- Push row 1, rho8: new row = rho8(b,u,a,c). To produce rho8(A,B,C,U), choose
  global `(a,b,c,u)=(C,A,U,B)`.
- Push row 2, rho7: new row = rho7(b,c,a). To produce rho7(A,B,C), choose
  `(a,b,c)=(C,A,B)`.
- Push row 3, rho6: new row = rho6(a,c). To produce rho6(A,B), choose a=A,c=B;
  the unused b,u are arbitrary. The stored map swaps b,c on the full three-
  coordinate environment, so it really is a permutation even though rho6
  mentions only two coordinates.
- Push row 4, rho5: new row = rho5(b,c,a). Choose `(a,b,c)=(C,A,B)` for target
  rho5(A,B,C).
- The other four logical rows are unchanged.

Each new row is an old axiom instance (soundness), and the displayed inverse
choices produce every old instance (completeness). Every argument here ranges
over all natural numbers; there are no fresh-variable or decoded-formula
restrictions. The axiom families, and consequently their generated numerical
calculus, are identical.

For an enumerator completeness block, first reset D=H=0, use these inverse
values as the AX fields, select the desired row by its unchanged stack
position, and perform the usual cleanup. The other rows and the bundle emitted
by that same AX need not have the same desired parameters: they are simply
other legitimate theorems and are discarded by cleanup. This observation is
why independent row reparameterizations do not need a single common inverse
map across all eight rows. GEN still uses the original dedicated U(a,old H)
entry. Bundle construction and both inequalities remain original. All changed
rows still have outer implication, so their values differ from 1 and the
first-F/MP-first arguments continue to apply.

## Executable boundary checks

`audit_permuted_rows.py` independently checks all stored maps are permutations,
reconstructs all changed formulas from the original pinned specification, and
checks the complete symbolic emission stack against those formulas and the
unchanged selected bundle. It checks the unchanged GEN prefix and control
tail, exactly one explicit u-read, grammar expansion, emitted row count 534,
and table hash. Results are in `permuted_rows_independent_audit.json` and `.log`.
These checks passed with assertions enabled.

The ordinary proof above is about source semantics. The actual literal table
still needs its full reachable-domain simulation and bootstrap theorem before
being called an exact blank-tape Con(ZFC) machine. Existing source/table proofs
cannot be applied to the changed table solely because the formula families
coincide. The reported improvement from a matched 268-state compiler control
to 267 is useful engineering evidence, not a sub-246 result or a claimed global
state optimum.

No producer artifact, shared checkout, external repository, or user computer
was modified during this review.
