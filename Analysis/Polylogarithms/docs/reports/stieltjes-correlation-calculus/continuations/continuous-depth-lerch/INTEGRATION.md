# Integration note

## Relationship to existing work

Add this package as the continuation answering Section 12, question 10
(noninteger convolution depth) of *Reciprocal Lerch Convolutions*.
Do not replace that report or claim its integer-depth results as new.
The maintained canonical manuscript should be edited only in a separate,
reviewed integration step, not automatically by this delivery.

Suggested relative location beneath the reciprocal-Lerch continuation:

```text
continuations/continuous-depth-lerch/
```

This is a recommendation, not a claim that this path exists. Resolve the actual
parent on the Mellin–Stieltjes thematic spine using the pinned/current intake
rules. Preserve the delivered package and compiled PDF according to those rules.
All LaTeX equation, section, and theorem labels have the prefix `cdl:`.

## Claim-status update proposed for review

- Q10 has an explicit Gamma-kernel solution on Re(rho)>0, jointly holomorphic
  with the shift and entire in the spectral order. Ordinary convolution adds
  both parameters. Negative/zero depth requires a further distributional study.
- The complete continuous-depth moment algorithm and continuous-split Stieltjes
  product laws are proved conventionally in the accompanying article.
- The harmonic coefficient master and odd-polylogarithm Gamma family are proved;
  precise literature-priority labels remain subject to independent reconciliation.
- Integer total-depth finite formulas, classical Gamma transforms, and several
  low-weight Euler sums are recoveries, not newly claimed discoveries.
- A monodromy obstruction applies to the specified locally meromorphic transform
  class only. It implies no arithmetic independence of special constants.
- No error was established in the source proof sections inspected. The safeguards
  for complex depth, negative orders, resonances, and unequal moment coefficients
  are additions, not unsupported errata against prior authors.
- The Gaussian S6 and S8 candidate status is unchanged.

## Review order

1. Read the analytic kernel and spectral-extension proofs (Sections 2–3).
2. Review the Gamma-quotient normalization and harmonic coefficient proof
   (Sections 5–6), including the 2^(rho-2) and 1/2 factors.
3. Check the first/second moment reductions and Stieltjes signs (Sections 7–8).
4. Review the precisely defined monodromy class (Section 11).
5. Run the verification on a separate copy; compare the recorded receipts.

The exact finite-algebra layer is a natural proof-assistant target. It does not
currently have Lean or Rocq certification. The analysis layer requires weighted
function-space holomorphy, Fourier inversion, and Mellin subtraction.
