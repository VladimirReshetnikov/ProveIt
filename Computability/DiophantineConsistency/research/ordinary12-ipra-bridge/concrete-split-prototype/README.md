# Historical model-level split for the exact 100-row literal

For every four integer ports and every valuation in any `IΣ₁` arithmetic
model, `literal_factor_units` proves that an internal zero of the 100-row
literal forces each of its three exact signed factor pairs to represent +1.
The theorem has no port, positivity, or rank assumptions. Lean proves the
three bindings to the expression-shaped residue exclusions by definitional
identity. The first and main exclusions use the audited historical `first_bad`
and `main_bad` lemmas; the ordinary exclusion uses a finite modulo-four
calculation with its explicit even second coordinate.

`check_binding.py` checks that the parts graph is textually identical to the
already checked literal, verifies its exposed parts and theorem bindings, and
rejects three mutations. Its nested graph check verifies all 100 rows and
rejects four more mutations. This is source validation outside Lean; Lean's
factor and model theorems are checked separately.

Fresh replay session 82959 actually exited 0 and printed
`PASS_BOUNDED_ORDINARY12_CONCRETE_SPLIT
97aa4b119f8b37a3afb8bb4cafc2c0b8e03db233eb734a67b1fe23ce8fa36572`.
The receipt records the exact compiler reports, direct dependencies, source
and object hashes, inherited source-declared overlay and post-use seed and
companion checks. The fresh run rebuilds the previously recorded abstract
split before compiling the literal, expression-pattern exclusions, and
concrete split. It is a single-author historical replay, not a matched full
project replay or a package-transitive/dynamic dependency audit. The original
warning-bearing attempt and the failed namespace-shadow attempt are recorded
in `observations/`; the clean source suppresses the unused-binding linter for
the duplicated graph while retaining all rows and the same theorem.

The four ports are still symbolic here. Separately checked provenance binds a
particular compact44 tuple, including β = 2^590069 − 1, but does not prove its
checker calibration. The older fixed 2011 endpoint uses β = 2^94517 − 1 and
cannot be substituted. Rank reconstruction, ordinary norm recovery, transport
to the shorter 95-gate literal, both directions of consistency equivalence,
and an object-level iPRA proof remain open. A model theorem alone is not a
Lean proof that iPRA proves the statement.
