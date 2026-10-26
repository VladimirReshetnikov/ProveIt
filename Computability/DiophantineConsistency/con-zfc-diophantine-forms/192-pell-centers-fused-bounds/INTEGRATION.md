# Integration note

Snapshot: `b42c796d1f5de9912a576bc2fd77b778ae7402bf` of
`VladimirReshetnikov/ProveIt`.

Suggested destination: a newly numbered directory under
`Computability/DiophantineConsistency/con-zfc-diophantine-forms/`, assigned
at intake. No remote repository mutation was performed by this task.

Recommended index description:

> Polynomial-center Pell growth gives 212 unrestricted integer variables,
> degree four, 152 residual squares, height 6,432 and 21,556 monomials;
> its sparse companion has 5,290 monomials and height 277,420. A fused
> Pell-cap/remainder guard and linear orientation give 82 variables at
> degree 16,964 / 1,723 operations, 81 at degree 2,097,732 / 1,711, and
> 106 at degree 32 / 1,830. A second Pell-root quotient carrier gives
> 13 positive variables / 69 operations / degree 174 and a 39-integer
> lift / 160 operations / degree 348. Ordinary new proofs and exact
> artifact verification compose with the explicitly inherited calibration.

Important distinctions for integration:

- The 212-variable small-coefficient quartic and its sparse companion have
  the same integer zero set but different expanded polynomials.
- The 82-, 81-, and 106-variable constructions share a separate exact
  immediate source. They do not yet incorporate the new polynomial growth
  center. Simply combining their dimension savings would be unsupported.
- The compact thirteen-variable equations require strictly positive
  inputs. Their explicitly supplied 39-variable lifts are unrestricted.
- Source constants are complete and source-bound. The admissible942
  tuple must not be mixed with the indexed943 or another native tuple.
- An exact degree, an exact expanded height, a conservative height upper
  bound, and the largest circuit literal are different measurements.
- New semantics are ordinary proofs formalizable in ZFC; a fresh full
  proof-assistant endpoint remains a further task.
- Comparisons are pinned and measured. The submission establishes neither
  global minimality nor literature-wide priority.

Review order: report, ordinary proof review, component provenance, finite
verification, then literal equations and independent-degree certificates.

Run `python3 -B verify.py --checksums` from a fresh extraction. The report
includes a complete literal appendix for the principal quartic. All new
code uses the Python standard library. TeX Live builds the report.

Selected upstream proof sources under `quartic212/upstream/` are an
attributed reference subset, not a copy of the entire old release. Its
historical README may refer to files in the original release; use the
new top-level verifier for this package. The complete immediate projected
parent is separately frozen as `projected/sources/parent_archive.zip`.
