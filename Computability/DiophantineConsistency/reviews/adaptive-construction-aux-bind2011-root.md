# Binding the auxiliary ordinate to the adaptive witness

`ArithmeticAdaptiveConstructionAuxBind2011.adaptive_auxiliary_of_phase`
works in every IΣ₁ model. Given the actual 14-coordinate equation system,
the rank congruence `rank v % 4 = 3`, and an explicit identity saying that
coordinate 12 is the Pell ordinate at that rank, it constructs a positive
adaptive auxiliary coordinate `u` with `u + Vabs = v 12`. This composes the
existing auxiliary norm with the phase bound; it does not derive the phase or
the ordinate identity from an arbitrary solution, nor does it complete the
reverse construction.

Two independent source-current builds of the theorem and its axiom checks
passed against the independently replayed 18-module adaptive provider at
`/tmp/adaptive13-sandwich-postmerge-8tly07ke/lib`. Source, object and full
log hashes match. The builds report only `propext`, `Classical.choice` and
`Quot.sound`. Their [18-file evidence manifest](adaptive-construction-aux-bind2011-evidence/FILES.json)
has SHA-256 `f63d5dfe46a6aa2f451876fe76b2e2cb4f58bb0017744c9c08de51d636dde4d5`.
The inherited provider and package qualifications in the [Sandwich replay](adaptive-sandwich-postmerge2011-author.md)
continue to apply; this is not a fresh transitive rebuild.

After these builds, an upstream merge changed HalfBinomial and adaptive
population. The recorded provider is the preceding snapshot and must be
refreshed before claiming current-source coverage.

The affected provider was subsequently rebuilt and independently replayed.
Two further AuxBind builds against that refreshed provider passed at
`/tmp/adaptive13-construction-aux-bind-ranklower-ri9h7ctd` and
`/tmp/adaptive13-construction-aux-bind-ranklower-2mf2ooi9`, with matching
source, object and complete-log hashes. The [18-file refresh evidence](adaptive-construction-aux-bind-ranklower-evidence/FILES.json)
has SHA-256 `a374249454f69f2a64fba5772842a5b369dbb434bf2c88aa0ed7f9135e7b8cda`.
The prior inherited-provider and theorem-scope qualifications still apply.
