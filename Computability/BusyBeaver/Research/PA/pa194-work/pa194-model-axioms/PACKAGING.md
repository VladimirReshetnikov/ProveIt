# Conditional packaging of an internal ordinal-induction sequent

`ordinal_code_of_induction_sequent` gives a concrete sufficient condition for internal provability of the existing `ordinalInductionCode p`, for arbitrary internally valid arity-one p (including nonstandard codes), in an arbitrary internal Δ₁ source theory. The hypothesis is an internal derivation of the one-sided sequent

```
{ ¬ ordinalStepFromProperty(..., p),
  inductionConclusionCode(..., p),
  ¬ inductionBaseCode(..., p) }.
```

The omitted arguments in this display are the actual typed domain, zero and successor templates shown explicitly in the theorem source. `packageInductionProof` implements the final two disjunction introductions as an actual typed internal proof constructor; `package_induction_derivable` is the general numeric-code version. The internal derivability of the displayed sequent is a **hypothesis**, not a conclusion established here. In particular, this source does not internalize the standard minimum-counterexample proof and does not establish an ordinal-induction theorem, an arbitrary PA proof compiler, or a native iPRA consistency implication.

The model assumptions are a nonempty candidate-PRA model with IΣ₁ on its induced ordered ring. `Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-packaging.sh "$REPO" FRESH_OUTPUT` recompiles the source against the repository-replayed ordinal and typed-schema prerequisites and the prebuilt transitive overlays listed in the script. Source and immediate object hashes and three axiom reports are checked. Passing output `/dev/shm/pa194-induction-packaging-replay`; log `/tmp/pa194-induction-packaging-replay.log`.
