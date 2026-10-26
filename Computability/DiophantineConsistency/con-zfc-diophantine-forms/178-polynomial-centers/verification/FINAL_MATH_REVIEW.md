# Final mathematical and attribution review

Review date: 2026-10-26 (UTC).

This is an additional AI-assisted internal review of the submission. It is
not an outside human review, a proof-assistant certificate, or a new
end-to-end verification of the inherited consistency calibration.

## Scope and conclusion

The final `README.md`, `whole_product/PROOF.md`, and `report/main.tex` were
read for consistency with the mathematical constructions and the stated
verification boundary. No material mathematical limitation was found to
be omitted. The principal result is a polynomial with ten independent
**strictly positive integer** variables, exact degree 208, and a literal
116-operation evaluation graph using the specified four fixed integers.
The equivalence with `Con(ZFC)` is an ordinary mathematical argument
formalizable in ZFC, composed with identified inherited arithmetic and
refutation calibrations. It is not a newly compiled Lean/Rocq theorem.

The direct quartics use a separate proof-calculus route and explicitly
state their different domains. The natural-variable equations quantify
over nonnegative integers; the integer equations quantify over all
integers. Their row and variable counts are not substituted for those of
the ten-positive-variable construction.

## Principal proof checks

The detailed mathematical audit is recorded in
`REVIEW_WHOLE_PRODUCT_CENTERS.md`; the following identifies the points
that are material to the final packaged statement.

1. The displayed factored center

   `Omega = U*(2*S*Rc + A*(4*E*V - theta*Sc))`

   agrees with the final center used by the 116-operation graph. It is an
   integer polynomial. The notation for quotients of the polynomial
   `E(t)*V(t)` is used only in its proof; it introduces neither a numeric
   floor operation nor an extra existential variable.

2. The quotient `Q3` is coefficientwise even: the summand
   `E(t)*(b-c)` has degree at most two and contributes nothing to that
   quotient, while the remaining summand has the factor `2*U^2*b`.
   Consequently the proof identity

   `Omega = U*(4*A*E*V - 2*Q1 - Q3/2)`

   is compatible with the division-free delivered formula.

3. The coefficient-majorant argument is valid before the semantic signs
   of `B`, `C`, and `R` are known. In particular, it yields the sign of
   `Omega` from the sign of `V`, rather than presupposing positivity of
   the center. Its quantitative conclusion is

   `3*A*U*E*|V| < |Omega| < 5*A*U*E*|V|`.

4. The scaled-root and center budget

   `4*g*y + |Omega| < b^2/4`

   follows from the recorded estimates. The last step uses
   `|b| > 7*f^3` and `f > 2`; these hypotheses are sufficient because
   `27/(56*f) < 1/4` already follows from `f > 27/14`.
   There is no missing stronger lower bound at this step.

5. The exclusion of `B <= -1` uses the square weight `L=b^2`, the
   preceding budget, and the inverse-Lucas bound valid for every integer
   `R`. It does not use the mask's positive-rank bound prematurely. The
   integer center preserves the later congruence handoff. The factor 3
   at the full denominator is canceled only after the required power-of-two
   information has been established.

6. Completeness uses the retained canonical witnesses with positive
   `V`, hence positive `Omega`, and defines the final positive input `n`
   explicitly. The final manuscript correctly refers first to the Pell
   equation in the adjacent-Pell display; it does not assume the carrier
   identity before `n` has been chosen. The argument does not assert that
   arbitrary integer shears preserve positivity.

7. The total-degree calculation accounts for the full output, including
   the cross term. The weighted norm defect has exact degree 106 and top
   form

   `8*A^8*Y^8*k^8*U^6*b^2 - 48*A^6*Y^12*k^8*U^6*b^2`.

   The complete output's successive degree bounds are
   `122, 177, 208, 152, 72`. The unique degree-208 contribution is
   nonzero after substitution of the actual positive fixed `beta`.
   Thus 208 is an exact degree, not merely a syntactic upper bound.

The package's `whole_product/CHECK.json` and
`whole_product/INDEPENDENT_REVIEW.json` record successful exact algebra
checks, including the final graph, the 84 center monomials, the 594 norm
defect monomials, the fixed numeral identities, and the leading form.
Those finite checks have a different scope from the unbounded estimates
and the inherited logical calibration. This distinction is stated in
both the article and the plain-text proof.

## Direct natural projection checks

The separate review `REVIEW_NATURAL203.md` records the direct natural
equation audit. In particular, the first two eliminations use the source's
canonical positive lifts; they are not asserted to be bijections on all
old natural zeros. The third elimination is a pointwise natural
zero-set bijection because a retained row forces the restored coordinate
to be `T*(T+1) >= 0`. Its polynomial's negative coefficients do not
invalidate that argument. The source calibration and exact row identities
remain necessary parts of the result.

## Attribution and the novelty boundary

Whole-expression polynomial centers are already present in the inspected
repository's eleven-unrestricted-integer branch. Three concrete sources at
commit `fb1bed5eb7196cf35abfaa746c18c6ee7eae6cfb` are:

- `153-nearest-factorial/signed/PROOF.md`, section 6, “Eleven variables
  and a further center correction.”
- `154-normalized-residues-round19/report/scalar.tex`, the section
  “Polynomial centers and eleven integer equations”; its scalar README
  and fixed-frame degree-floor note further delimit that branch.
- `165-wider-budgets-round20/scalar/PROOF.md`, “Compressed
  whole-expression centers: eleven unrestricted integers.”

All three paths are relative to
`Computability/DiophantineConsistency/con-zfc-diophantine-forms/`.
The final README and the article now acknowledge these antecedents.
The defensible contribution here is the explicit `EV` quotient center in
the ten-positive-variable trace/inverse-Lucas frame, the bound required
before semantic signs are recovered, and the resulting literal degree-208
endpoint. It is not the general idea of using polynomial centers or
integer shears. No exhaustive worldwide priority claim is supported by
this audit.

The proposed fixed-label seed/vacuity split was also checked against
package 156's existing negative experiment. It is correctly not promoted
as a new construction or used to justify the delivered improvements.

## Material limitations retained in the submission

- No global minimum is proved for degree, operation count, number of
  variables, coefficient size, or any combined notion of simplicity.
- The compact construction retains native/K215 ancestry. The direct
  C222 quartics supply the distinct route.
- The compact coefficient tuple is the exact inherited tuple. Merely
  substituting four numerals satisfying elementary size inequalities is
  insufficient for its refutation calibration.
- Large fixed coefficients are an explicit part of the compact result.
  Its binary-operation count is a graph metric, not a measure that
  includes writing every bit of each fixed numeral.
- The new Diophantine bridge and inherited proof-assistant developments
  have not been jointly compiled as an end-to-end formal theorem.
- The argument neither assumes nor proves the truth of `Con(ZFC)` and
  does not supply a zero of any consistency polynomial.
- Internal AI-assisted review and exact finite replay are not described
  as independent human peer review or as a substitute for the unbounded
  proof.

The final verification manifest and top-level source snapshot are
packaging outputs and should be regenerated after this review file is
added. This review does not attest to the identity of a ZIP created after
the audit; that is the purpose of the final manifest and replay receipt.
