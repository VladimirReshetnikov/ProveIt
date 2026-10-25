# Frozen construction stages

All paths below are relative to the extracted package root. No heuristic search
needs to be rerun: `python3 -B verify.py --rebuild` checks the frozen chain.

1. Parent: `inherited/parent225/equation/equation.json`.
2. Five common-Hessian projections:
   `stages/radical220/equation.json` and
   `projection_certificate.json`.
3. Small integral affine chart:
   `stages/lattice219/equation.json` and
   `affine_lattice_certificate.json`.
4. Unit affine graph projection:
   `stages/affine218/equation.json` and
   `projection_certificate.json`.
5. Protected residual basis, final quartic:
   `equations/quartic218/equation.json`, `row_certificate.json`,
   `protection.json`, `metrics.json`, and `expanded_polynomial.json`.

Each intermediate directory also contains its complete expansion and exact
metrics. Stage 4 was serialized with indentation by the inherited producer;
its certificate uses raw SHA-256. The other transformation certificates use
canonical compact JSON with sorted object keys, one final newline, and
unchanged list order. The distinction is explicit in the checkers.

Independent verification code is `code/audit_transformations.py`; receipts are
under `verification/`.
The `code/build_reciprocal.py` reciprocal-pooling builder consumes the final protected218
and produces the lower-variable degree-ten companion. Its construction is
existentially equivalent by the separately proved arithmetic theorem, rather
than a global polynomial coordinate bijection.

## Producer scripts

- `inherited/projection159/code/reduce_radical.py`: exact search and
  projection producer; inherited from package159 with its NOTICE and LICENSE.
- `code/lattice_affine.py`: deterministic integer chart producer;
  exports complete forward and inverse maps and the explicit affine row identity.
- `inherited/projection159/code/affine_project.py`: inherited unit affine
  consequence substitution; depends on `affine_search.py`.
- `inherited/projection159/code/reduce_basis.py`: inherited row-reduction
  discovery procedure; the frozen 669-step certificate is sufficient for replay.
- `code/protect_pool_rows.py`: replays the original 670-step
  certificate while omitting its single pool-changing operation [152,106,1].

Optional discovery commands, shown with disposable destinations. The frozen
certificates, not a new heuristic run, define the delivered endpoints:

    python3 -B inherited/projection159/code/reduce_radical.py inherited/parent225/equation/equation.json /tmp/conzfc-discovery-radical
    python3 -B code/lattice_affine.py stages/radical220/equation.json /tmp/conzfc-discovery-lattice
    python3 -B inherited/projection159/code/affine_project.py stages/lattice219/equation.json --output-dir /tmp/conzfc-discovery-affine
    python3 -B inherited/projection159/code/reduce_basis.py stages/affine218/equation.json /tmp/conzfc-discovery-row-basis
    python3 -B code/protect_pool_rows.py stages/affine218/equation.json /tmp/conzfc-discovery-row-basis/row_certificate.json /tmp/conzfc-discovery-protected

The complete provenance and dependency restoration notes are in
`PARENT_PROVENANCE.md`. Two parent release checkers were replayed rather than
merely carrying their historical receipts into the new submission.

The finished reciprocal equation is `equations/decic215/`. Its certificate
records the exact four private coordinates, four removed rows, affine bases,
shared Pell parameter, numerator polynomials, and coordinate reindexing.
