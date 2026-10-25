# Direct unrestricted integer quartics in round 17

The final direct family contains three exact degree-four equations over unrestricted integers:

- `strict_dimension_centered`: 282 variables, 192 quadratic residuals, 5491 collected monomials, coefficient height 128446.
- `strict_grouped_centered`: 287 variables, 197 quadratic residuals, 4313 collected monomials, coefficient height 128446.
- `strict_sparse_centered`: 309 variables, 219 quadratic residuals, 3922 collected monomials, coefficient height 128446.

Each equation is exactly the sum of its listed residual squares, and every collected coefficient is supplied. The first strictly improves the prior 324-variable endpoint in variables, rows and support at unchanged height. The grouped point also strictly improves the prior sparse 338-variable endpoint in those three counts at unchanged height. The last trades variables and rows for still smaller support. None is claimed globally minimal.

The full ordinary proof is divided into three local, complete parts rather than abbreviated into a claim of a successful finite test:

1. `PROOF_315.md` proves signed-center Pell frames, semantic-anchor reuse, the squared signed cap, the explicit even-anchor odd auxiliary construction, and cofinal completeness. Its 315-variable count belongs to the conservative checkpoint stated there.
2. `ORIENTATION_FIRST_PROOF.md` removes ten front sign graphs by recovering both canonical coordinates, handling negative and zero requested indices, interpreting actual nonnegative representatives rather than falsely restoring shifted coordinates, and repairing the zero-representative radix bound. Its intermediate measured counts are explicitly labeled.
3. `STRICT_BUDGET_PROOF.md` proves the final K=x amplification, strict beta quotient ranges, seed merger, grouped and sparse variants, and final metrics. It replaces the older K=2R schedule only where expressly stated.

These parts are meant to be read in that order. They retain the full round16 arithmetic-front and C222/ZFC-refutation calibration dependencies, whose authenticated package is preserved by the release closure. The copied exact constructor sources and hashes are in `constructor_sources/`. The finite checker reconstructs the source changes and every collected polynomial coefficient independently of the producing compiler. It is run both normally and under -O.

The resulting theorem is that ZFC proves integer unsolvability of each fixed equation equivalent to Con(ZFC). This does not prove Con(ZFC), establish a global minimum, or claim a newly compiled end-to-end proof-assistant derivation.
