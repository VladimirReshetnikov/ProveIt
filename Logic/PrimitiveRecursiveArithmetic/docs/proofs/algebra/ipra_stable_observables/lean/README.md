# Compiled proof combinators and a spectral blueprint

This small Lake project compiles `ObjectObservation.lean` against the exact
unmodified `Syntax.lean`, `Deduction.lean`, and `PR.lean` declarations from
ProveIt commit `c39c388d4f87220ab9e758ae457520bbc0d74341`.

The pinned toolchain is Lean 4.32.0 and the pinned Mathlib revision is
`81a5d257c8e410db227a6665ed08f64fea08e997`. Only the dependency closure of
`Mathlib.Data.Fin.Tuple.Basic` is needed. Dependency binaries and `.lake/`
are not included.

## What is proved

All five declarations below return the actual embedded `Prf PRAAx` type:

- `boundedInvariantAt`: specialize permitted quantifier-free induction at
  an explicit numerical fuel term;
- `loopProducesCertificate`: extract a certificate from the terminal invariant;
- `observableOfIndependentCertificates`: combine two certificate derivations
  with their supplied observation comparison;
- `observableFromLocalStability`: the same cut rule with local hypotheses;
- `twoLoopsStableObservable`: assemble two finite loops and a stability proof.

They implement common logical plumbing. The matrix identities, energy
inequality, PR program reification and spectral comparison proofs are separate
formalization tasks. This project does not assert that the spectral theorems
have been fully formalized in iPRA.

## Reproduce

With Elan installed and network access for the pinned dependencies:

```sh
bash build.sh
```

The included `validation/` directory records the successful build, exact Lean
version and axiom audit. The checked combinators depend only on Lean's
`propext` and `Quot.sound`; none depends on `sorryAx` or `Classical.choice`.
These are metatheoretic Lean dependencies, not new axioms of embedded iPRA.

## What is specified but not proved

`SpectralBlueprint.lean` uses `Std` alone and defines finite rational
vectors/matrices, a recursive finite sum, matrix operations, Frobenius squared
norm, and the exact rational Jacobi algorithm with its explicit fuel and final
sorting. Certificate data have no proof fields; their validity is specified by
separate formulas. `PositiveCertificate` is a rational weighted Gram / LDL
factorization with nonnegative weights, rather than a rational orthogonal
diagonalization.

The file also defines explicit target propositions for pivot improvement,
energy preservation/progress, the fuel theorem, cross-input sorted spectral
comparison, positivity certificates, square-root comparison in mixed bases,
threshold projectors, and certified gap-to-margin transfer. These propositions
and the `UnprovedMatrixObligations` structure are **not instantiated**. Their
successful type checking is not a proof of the mathematical targets.
`RootProducerTarget` and `PositiveProducerTarget` specify correctness of future
producer functions; their PR syntax and arithmetic proof must also be supplied.

`SpectralAudit.lean` records that these host rational definitions inherit
`propext`, `Classical.choice`, and `Quot.sound` from Std. No new axiom is
introduced, and these dependencies are not an assertion of extra axioms in
embedded iPRA. Its audit checks the definitions and evaluates one finite 2-by-2
example, whose sorted values are `26/25, 74/25` and squared off-diagonal
residual is `98/625` at requested tolerance `1/2`. This execution example is
independent of the universal, still-unproved target propositions.

## Integration

Inside the corresponding ProveIt checkout, retain only the new
`ObjectObservation.lean` and optional `ObjectAudit.lean`. The import
`ConciseIPRA.PR` then resolves to the repository's existing library. The
three upstream copies here make the small standalone package reproducible;
their source hashes and pinned identity are in `upstream_manifest.json`.

After obtaining a particular `Prf PRAAx` derivation, ProveIt's
`pra_iff_native.mp` transports it to the native scalar calculus. That final
bridge is not used to convert an arbitrary ambient Lean theorem into an
iPRA derivation.
