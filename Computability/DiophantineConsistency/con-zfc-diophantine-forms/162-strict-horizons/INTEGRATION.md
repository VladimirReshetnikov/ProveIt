# ProveIt integration notes

## Proposed placement

Preserve the complete release archive as:

```text
docs/incoming/ConZFC_Strict_Horizons_2026-10-25.zip
```

After review, a suitable extracted location is:

```text
Computability/DiophantineConsistency/con-zfc-diophantine-forms/strict-horizons-2026-10-25/
```

Keep the package's relative directory structure. It connects the current
equations, exact transformation certificates, coefficient payloads, ordinary
proofs, and inherited source dependencies. In particular, copying only the
expanded polynomials would omit the provenance and verification needed to
assess the consistency equivalence. No repository push or publication is
part of this release.

## Recommended catalog entries

Record the principal direct equation as:

> **Strict Horizons, 25 October 2026.** Explicit quartic over 236 unrestricted
> integer variables, presented as 173 squared quadratic residuals; 4,876
> collected monomials; coefficient height 7,968. Ordinary proof, exact
> transformation certificates, independent finite checks, and retained
> calibration dependencies supplied. Matched factorial-free parent:
> 242 variables, 178 residuals, 5,018 monomials, height 7,968.

Record its companion as:

> **Strict Horizons, dense companion.** Explicit quartic over 235 unrestricted
> integer variables; 172 quadratic residuals; 12,566 collected monomials;
> coefficient height 7,968. Matched factorial-free parent: 241 variables,
> 177 residuals, 12,774 monomials, height 7,968.

Record the compact results separately:

> **Free Quotient Scale.** Two explicit polynomials over ten strictly positive
> integer variables: 83 binary operations at exact degree 312, and 89 binary
> operations at exact degree 278. Complete fixed coefficient payloads,
> deterministic reconstruction, independent exact checks, and ordinary
> soundness/completeness proofs supplied. The large fixed coefficients and
> native/BFS943 ancestry are retained.

The 236-variable direct form is the recommended small-coefficient endpoint.
The 89-operation, degree-278 form is the recommended compact expression
within this release. Preserve their different domains and metrics in
comparison tables. Neither entry should be labeled globally smallest.

## Mathematical review points

The report proves both directions of the existence equivalence and identifies
the inherited C222/ZFC or native/refutation calibration. The main changes to
check are:

1. The five strict local ranges share `q^t`; deleting the private `t+1`
   certificate removes no remaining power dependency or frame requirement.
2. At `F=t^t`, the matched positive coefficients lie in `[1,F]`, so
   their differences have absolute value below `F`, even at the equality
   boundary. The new strict ranges are more than sufficient for this proof.
3. `lcm(1,...,t)^2<F` validates the reduced CRT radius, including the
   completeness assignment for every prime factor of the modulus.
4. The affine radix `q=4z+1` receives a sign-independent bootstrap before
   positive digit recovery is invoked.
5. Completeness for `F=t^t` chooses **even `h`** in `t=16+h^2`, a strict
   horizon beyond all finite local values, and fresh compatible witnesses.
6. The compact construction restores its denominator after projection and
   preserves the factor six in the corrected projector. Its converse uses
   fresh witnesses at `lambda=q`.

Retained historical notes describe their own ancestors. Their old metrics,
growth bases, and parity choices should remain attributed to those ancestors;
the current report and current literal equations define this submission.

## Reproduction and editorial checks

From the extracted package root, run:

```sh
python3 -B verify.py
python3 -B -O verify.py
```

The report source is `report/main.tex`, and the supplied compiled report is
`report/main.pdf`. Keep the complete verification receipts and transformation
certificates alongside the equations. When moving the package, rerun the root
verifier to catch broken relative paths or omitted source files.

For the direct catalog entries, confirm domain `unrestricted integers`, exact
degree four, collected support, and maximum absolute collected coefficient.
For the compact entries, count independent positive variables and live binary
arithmetic operations; do not count polynomial abbreviations as variables or
treat large coefficient payloads as free storage. Preserve exact polynomial
identity checks separately from the unbounded arithmetic proof.

## Attribution and acceptance status

Retain the source snapshot identifier
`7a8da414376a80b90ecf799f37ceb26fb9ac674e`, all source pins and notices, and
the licenses accompanying `sources/` and `compact/upstream_lucas/`. Credit
Factorial Free Binomial CRT, Shared Factorial Error, Cofinal Witnesses and
Centered Carriers, and Lucas Corrections and Witness Elimination, together
with their retained predecessors.

The direct C222 route and the compact machine-derived route have distinct
ancestries. Do not describe the compact result as eliminating the native
machine encoding, or describe the direct result as depending on K215.

Suggested incoming status: **candidate with supplied ordinary proof and exact
artifact verification; repository review pending**. The release makes no
claim of global optimality, new end-to-end Lean/Rocq certification, an emitted
object-language ZFC proof, or a proof of ZFC's consistency. Acceptance and any
changes to existing “current best” repository entries remain maintainer
decisions.
