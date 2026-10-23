# Proposed incorporation in ProveIt

Repository baseline: `4b4349064a750ba6347293b55874a7f92abdd0db`.

## Suggested placement

Place this directory under the next available construction identifier in
`Computability/DiophantineConsistency/con-zfc-diophantine-forms/`, using a
descriptive suffix such as `congruence-norms`. The package deliberately does not
reserve a numeric identifier because incoming work may be incorporated in a
different order. The ZIP may first be copied into `docs/incoming/`.

The report and generated primary circuits are the main deliverables. Retain
the manifests, fixed integer data, independent checks, and inherited notices.
Do not replace the current formally verified local candidate merely on the basis
of a smaller numerical ledger; its formal status is a separate metric.

## Frontier entries to add

| Domain | Variables | Exact degree | Operations | Result |
|---|---:|---:|---:|---|
| Unrestricted integers | 10 | 9,152,284 | 586 | Coprime square/positivity guard and two-root norm |
| Positive integers | 9 | 5,671,669 | 630 | Congruence separation and higher polynomial majorant |
| Positive integers | 9 | 6,692,108 | 604 | Congruence separation and cheaper majorant |
| Nonnegative integers | 9 | 5,671,669 | 636 | Natural translate of the higher-majorant form |
| Nonnegative integers | 9 | 6,692,108 | 610 | Natural translate of the cheaper form |
| Positive integers | 14 | 52 | 79 | Auxiliary gap and squared-modulus quotient |

The two nine-positive points are both useful. The degree-5,671,669 form uses
26 more operations than the cheaper variant. Existing points with still fewer
operations and larger degrees remain in the comparison. The 14/52/79 result
dominates the incoming 14/56/79 point on these metrics; it does not dominate
the fifteen-positive degree-44 or minimum-operation forms.

## Formalization sequence

1. Parse the 22 original positive residuals and prove the factorial-weighted
   extraction identity with the corrected targets. The complete finite support
   certificate is small enough for a reflected or native-decide proof.
2. Prove the `1+g+ell` source substitution, coefficient bounds, positive leading
   source term, borrow invariant, and mask equivalence. Explicitly exclude the
   all-one source vector using residual 5.
3. Prove the universal congruence identities before assuming a zero of the
   final polynomial. For the integer route these include signed base values.
4. Prove the two-root rational extraction lemma, the coprime guard equivalence,
   and the recovery of `l != 0`. The `Sigma = 0` case must be discharged first.
5. Connect the new residue restrictions to the actual constructive Lucas
   choices, rather than postulating arbitrary congruence cofinality.
6. For nine variables, prove the positive majorants and the finalizer's integer
   offset bound; import the existing ratio theorem with its exact hypotheses.
7. Link each emitted fixed coefficient map and gate list to the mathematical
   definitions, then to the native source and calibrated K215 endpoint.
8. If the desired milestone is an object-language ZFC proof, separately export
   the consistency and unsolvability sentences and the internal derivation.

## Integration traps already addressed

- The unshifted 94-record support is not a subset of the old shifted support.
  Reusing the old code gives five cross-target interactions. Row 13 must use
  target 2124 and row 21 target 1059 in the delivered code.
- The source reversed polynomial has degree 5102 and leading coefficient 1;
  5190 is the maximum marked target, not its degree.
- `MF_source` is the shifted high-mask port. It is not `MF_native`.
- Natural variables, positive variables, and unrestricted integers are different
  supplied domains and must be shown separately in the frontier.
- The majorant certificate is `D^16` times the primary polynomial. Its degree
  and operation count must not be assigned to the primary evaluator.
- The finalizers use exactly two radicands. The elementary separation lemma
  does not justify the corresponding assertion for three arbitrary radicals.
- The ten-integer branch inherits Sun's 2026 theorem. The nine-positive route
  is the option if that additional dependency is undesirable.

## Validation boundary

The submitted finite audit passes without a network or Lean installation.
It does not search for a ZFC contradiction and cannot certify unsolvability.
The ordinary existence equivalence is the composition of the new proofs with
the inherited source, compiler, calibration and number-theoretic theorems.
No new end-to-end kernel verification or global optimality is claimed.
