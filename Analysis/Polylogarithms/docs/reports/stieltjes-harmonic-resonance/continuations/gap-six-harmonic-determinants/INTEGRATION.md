# Proposed integration

Base commit: c4036d60715916ae72dd18983782fdb182840b86.
No repository files were changed or pushed.

## Suggested destination

Add this complete package as a new continuation, for example:

    Analysis/Polylogarithms/docs/reports/stieltjes-harmonic-resonance/continuations/gap-six-harmonic-determinants/

The project can instead retain the ZIP in docs/incoming until review is complete.
The modular source is preferable for editing; the assembled source is convenient
for independent compilation and archival use.

## Source-status edits

### Ordered Boundary Identities and Gamma Kernels

Archive: ProveIt_Ordered_Boundary_Identities_2026-10-11.zip in docs/incoming.

Inner source: sections/09_audit_research.tex, the row for all unequal even
harmonic-tail prefixes and the first further-research question.

Proposed replacement status:

> Complete gap-six coverage is proved in the Gap-Six Reconstruction continuation.
> Its proof uses an explicit Gamma-integral threshold and an exact finite-field
> certificate for the complementary finite interval. The unrestricted all-pairs
> conjecture remains open. The stronger sign statement for every b >= 7 is
> separate: finite-field nonvanishing does not establish that sign.

The new main labels are gs:main, gs:Laplace, and gs:finite. Cite the new
ordinary-polygamma consequence at gs:ordinary.

### Bilinear Alternating Tails and Harmonic Determinants

Archive: ProveIt_Bilinear_Tails_and_Determinants_2026-10-11.zip in docs/incoming.

Inner sources: sections/05_degree_rank.tex and sections/10_research_questions.tex,
“Complex weights and sharp cutoff exceptions.”

Proposed update:

> Generic harmonic degree equals generic harmonic-pencil rank for every nonzero
> complex rational weight, with finitely many admissible cutoff exceptions.
> The proof is the rational symmetric primitive theorem in the new continuation
> (cr:primitive, cr:degree). The earlier real eventual-sign exception bound
> retains its real hypotheses; it is not replaced by a complex positivity claim.

The new coefficient-gcd criterion is the complex extension of the existing
criterion, not a new gcd algorithm. Preserve that attribution.

### Lattice Contacts and Mixed Zeta Identities

Archive: ProveIt_Lattice_Contacts_and_Mixed_Zeta_Identities_2026-10-11.zip
in docs/incoming.

Inner sources: sections/06_independent_shifts.tex and
sections/08_audit_and_research.tex, Q9.

Proposed update:

> The fixed-positive-rate collision a=lambda*epsilon, b=mu*epsilon is solved
> at every Stieltjes index and argument-derivative order. The complete joint
> singular expansion is urc:full-theorem, and its fixed-coordinate constant
> is urc:constant-theorem. Paths with a ratio tending to zero or infinity,
> nonlinear powers of epsilon, and three-factor contacts remain open.

## Conventions to preserve

- “Rank” for the moment-prefix theorem is rank on the specified formal labels.
- The late Bernoulli matrix omits a lower binomial index of zero.
- Complex symmetric matrices use transposition, not conjugate transposition.
- A collision constant is the coefficient of epsilon^0 (log epsilon)^0 in
  the named coordinate. Remove critical quotients before spectral derivatives.
- The modular certificate proves nonvanishing, not positivity.
- Classical Hahn/Christoffel and Euler-sum identities retain their cited attribution.
- Smaller-order ten and twelve are already completed source results.
- Do not change the conjectural status of short Gaussian S6 or revised S8.

## Audit conclusion

No newly false inherited mathematical theorem was identified in the dependencies
used. These are proposed status corrections and theorem extensions. No speculative
counterexample, arithmetic-independence claim, or unproved sign claim is introduced.
