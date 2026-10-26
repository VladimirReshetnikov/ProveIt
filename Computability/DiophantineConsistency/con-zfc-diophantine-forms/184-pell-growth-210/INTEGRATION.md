# Suggested ProveIt integration

This archive is prepared for incorporation into
`Computability/DiophantineConsistency/con-zfc-diophantine-forms/`.
No repository write or push has been performed. Choose the next numeric
catalog prefix at integration time; the inspected main snapshot ended with
source172, but that observation is not a reservation of the next number.

## Suggested entry title

**Pell growth from divisibility and an affine CRT radix: 210-variable quartic**

Suggested catalog summary:

> An explicit integer quartic in 210 unrestricted variables, presented as 150
> squares of quadratic residuals, with 5,282 collected monomials and coefficient
> height 2^40. Its non-solvability is equivalent in ZFC to Con(ZFC), by the
> supplied ordinary proof composed with the retained C222/ZF/ZFC calibration.
> Replaces exact exponential growth by a signed Pell ordinate forced large by
> divisibility, proves cofinal compatibility with the odd binomial selector,
> and uses the existing CRT index to define an affine radix. Includes exact
> coefficient replay, integer reconstruction maps and independent finite checks.

## Keep the metrics and domains separate

- Principal: 210 unrestricted integers, degree 4, 150 squares, 5,282 monomials,
  polynomial height 1,099,511,627,776, residual height 1,048,576.
- Balanced companion: 214 unrestricted integers, degree 4, 153 squares,
  5,699 monomials, polynomial height 91,679, residual height 192.
- Compact companion: 11 strictly positive integers, degree 174, 104 live
  binary arithmetic operations, largest fixed coefficient 592,884 bits.

The incoming archive's name contains 215, but its smallest-arity companion
already had 213 variables. The principal's correct comparison is therefore
213 -> 210. The balanced companion has higher support than its 215-variable
predecessor, despite its lower arity and unchanged height. The compact result
does not dominate the ten-positive-variable source172 on arity or gate count.

## Preserve the reproducible boundary

Retain the supplied paths under this package, including `inherited/anchor/`
and `compact11/`, for the offline verifier to work without network access.
If repository deduplication moves those dependencies, update the path bindings
explicitly and rerun both ordinary and `-O` verification from the new location.
Do not alter the authoritative equation JSON merely to change a display name;
its byte hash binds the reconstruction and finite receipts.

The principal is a direct C222 construction and has no K215 or Jones dependency.
The compact companion has its own native/compiler lineage. Label the results
as ordinary mathematical proofs plus exact finite verification, not newly
kernel-checked end-to-end formalizations. The mathematical article identifies
the inherited theorem boundary and the new lemmas that remain to be formalized.

## Integration commands

From the extracted package root:

```bash
python3 -B verify.py
python3 -B -O verify.py
python3 -B code/rebuild.py --output-dir /tmp/conzfc210-integration-rebuild
```

The output directory in the last command must be empty. To recompile the
article, run `pdflatex main.tex` twice from `report/`. The archive contains
the resulting PDF, so LaTeX is not needed to verify coefficients.

## Suggested follow-up formalization targets

1. Standalone Pell growth with center `4*t+1` and exact 2-adic index forcing.
2. Finite Pell permutations modulo powers of two and cofinal odd-binomial
   selector witnesses.
3. Pairwise coprimality of beta moduli from prime support alone.
4. Sign recovery and uniform binomial-tail authentication for the affine radix.
5. The changed arithmetic-source equivalence, composed with the numerical
   calculus and ZF/ZFC refutation endpoints.

These target the actual unbounded proof obligations. More bounded examples
would not replace them. Global minimality, historical priority and a proof
of Con(ZFC) are not claims of this package.
