# Dependency-ordered completion roadmap

1. Reuse the repository's term/formula/de Bruijn helpers where available;
   otherwise add tested `app1`/`app2`/`app3` helpers.
2. Select one code for Booleans, pairs, bounded lists, signed integers,
   dyadics, and positive-denominator rationals.
3. Build embedded Boolean folds and least bounded search with `PRA.qfInd`.
4. Complete `BaseFm`, `StepFm`, `FinalFm`, `InvRunFm`, and `ResultFm`.
5. Implement `traceReflection` entirely with `Prf` constructors,
   `PRA.precZero`, `PRA.precSucc`, and `PRA.qfInd`.
6. Verify a finite-sum vertical slice and transport it with
   `pra_iff_native`.
7. Implement bounded path codes, recursive viability, least viable paths,
   forward reachability, and backward tables.
8. Prove full viability equivalent to reachability plus backward viability.
9. Implement coded rational metrics and finite telescoping.
10. Complete the shrinking-viability theorem and regular-name corollary.
11. Add guarded arithmetic, robust overlap branching, finite nets, and
    height/list conversion.
12. Migrate representative exact, analytic, and relational theorem packets.
13. Run `lake build`, placeholder scans, and `#print axioms` on every public
    endpoint; record proof names in the theorem ledger.
