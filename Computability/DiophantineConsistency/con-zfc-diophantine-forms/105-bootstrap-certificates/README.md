# Factorial fixed points and smaller Diophantine consistency equations

Research submission for Vladimir Reshetnikov's **ProveIt** repository, 24 October 2026.

This archive supplies explicit single polynomials, complete ordinary mathematical
equivalence proofs, exact coefficient data, reproducible generators and independent
algebra checks. The new results compose with the identified inherited source
calibration to prove **in ZFC** that absence of solutions is equivalent to Con(ZFC).
No consistency assumption is used to select the equations or prove the equivalences.

Start with **`report/main.pdf`**. Its complete LaTeX source is `report/main.tex`,
with `report/metrics.tex`, `report/compiler_contracts.tex` and `nine/notes.tex`.

## Principal construction

The main unrestricted-integer equation is

    P_956(X_0,...,X_955) = sum_{j=1}^{510} r_j(X)^2 = 0.

Every quadratic residual is listed in
`integer/equations/integer956/equation.json`, and the **entire collected quartic**
is in `integer/equations/integer956/polynomial.json`. There are no free coefficient
parameters or remaining arithmetic macros. ZFC proves

    [there is no x in Z^956 with P_956(x)=0]  <=>  Con(ZFC).

The direct source is the C222 proof calculus with its pinned C222-to-ZF-to-ZFC
calibration. This component does **not** simulate K215 or use Jones' universal
polynomial. The separate few-variable components retain their own parent encodings.

### Direct quartic results

Here N includes zero, and Z means unrestricted integers. Every degree is exactly four.
Height means the maximum absolute coefficient of the **collected** polynomial.

| Equation | Domain | Variables | Quadratic residuals | Monomials | Height |
|---|---|---:|---:|---:|---:|
| `direct/equations/natural467` | N | 467 | 363 | 18,479 | 83,880,005 |
| `direct/equations/natural468` | N | 468 | 364 | 14,842 | 83,850,989 |
| `direct/equations/natural469` | N | 469 | 365 | 12,051 | 83,850,757 |
| `integer/equations/integer956` | Z | 956 | 510 | 10,988 | 2,445,790,974,704 |
| `integer/equations/integer989` | Z | 989 | 543 | 7,705 | 63,910,295 |

The 989-integer variant keeps every coefficient below 2^26 and has fewer terms;
the 956-integer variant uses fewer unknowns. The 467-natural variant uses a
different, independently proved factorial radius. These are intentional tradeoffs.

The immediately relevant direct baselines are natural522 (522 variables,
400 residuals, 20,225 terms, height 83,900,628) and integer1690 (1,690 variables,
842 residuals, 21,381 terms, height 2,649,643,805,758). In particular, the integer
comparison uses the newer incoming 1,690-variable construction. See `BASELINES.md`
for the exact files, domains, archive hashes, and qualifications. These are not
global variable-count records: the repository has much smaller variable counts
in other degree/coefficient regimes.

## The main new lemma

For every n,F in N,

    F = ceil( (F^2+1)^n / binomial(F^2+n,n) )  <=>  F=n!.

The proposed factorial supplies its own precision radius. Fixed-point uniqueness
is proved, not assumed. With K=n! and f(R)=K product_{j=1}^n (R+1)/(R+j),

    0 <= K-f(R) < K*n*(n-1)/(2R).

For n>=4, a fixed point first forces F>=n, then F>K/2, and then error <1.
The remaining n are proved explicitly. Completeness follows from error <1/2
at F=K. A single radius (H!)^2 serves every factorial argument <=H.
The alternative radius n^2F has an even shorter uniqueness proof.

The ceiling has the exact natural graph

    N+C=CF+r+1,   C=r+s+1.

The powers and binomials are replaced by finite polynomial graphs. A separate
variable-exponent radius certificate disappears from the actual materialization.
The power base F_H is proved positive from its unconditional base-modulus row
before factorial correctness is used, avoiding a circular argument.

Two further direct reductions remove locally determined premise labels before
bounded compilation, and infer integer coordinate signs from exact equations.
The integer construction uses 163 ordinary and eight paired ternary guards;
571 polynomial rules, 13 shifted-quotient rules, eight pair rules and 18 frame-root
rules cover all 781 original natural coordinates. Exact monic substitutions
then give the two final quartics. The independent verifier checks every sign
dependency, identity, substitution and final coefficient.

## Separate small-variable improvements

Arithmetic cost counts every live binary addition, subtraction and multiplication,
including squares and scalar multiplication. Fixed numeral leaves and register
reuse are free in this measure; it is not bit-operation complexity.

| Domain | Variables | New operations | Exact degree | Immediate comparison |
|---|---:|---:|---:|---|
| Strictly positive integers | 9 | 456 | 1,376,378 | 475 operations / degree 1,379,730 |
| Strictly positive integers | 9 | 442 | 1,520,186 | 433 operations / degree 1,628,768 |
| Strictly positive integers | 11 | 110 | 211 | 111 operations / same polynomial |
| Unrestricted integers | 13 | 176 | 1,408 | 185 operations / same polynomial |
| Unrestricted integers | 13 | 177 | 1,392 | 186 operations / same polynomial |
| Unrestricted integers | 13 | 186 | 1,088 | 195 operations / same polynomial |
| Unrestricted integers | 13 | 186 | 1,072 | 195 operations / same polynomial |

The nine-variable result uses the new strict majorant

    J=4A-5, D=1+(A^2-1)C^2,
    F=1+(A^2-1)D(iJC^2)^2,
    T=iC^2[AJ(2D-C^2)+3C^2-4] > 2 sqrt(DF)

for A>=2, C>=2 and i>=1. The boundary C>=2 is essential and implemented by
a successor coordinate; the canonical witnesses prove completeness. All fixed
numerals and each coherent four-port tuple are included in `nine/`.

The generic cleared radical norms use 18, 38 and 84 operations for three, four
and five roots. Their identities are proved by full coefficient comparison,
and complete parent substitutions are checked. `norms/` includes five literal
whole-polynomial evaluators and their exact coefficient payloads.

## Reproduce

Only Python 3.10+ and its standard library are required for mathematical checks.
No internet, repository checkout, solution search, or theorem prover is needed
for these commands:

```sh
python3 verify.py
python3 -O verify.py
```

They authenticate the archive manifest when present and run all components in a
temporary copy. They do not rewrite the delivered equations. An optional
`--receipt /path/to/receipt.json` stores the full release result. The standalone
component entry points and builders remain available; see their READMEs.

For just the main integer equation:

```sh
python3 integer/verify_integer.py \
  --parent direct/equations/parent781/equation.json \
  --equations integer/equations/integer956
```

To regenerate it, rather than merely check it:

```sh
python3 integer/build_integer.py \
  direct/equations/parent781/equation.json /tmp/integer956 --cap 16
```

Use `--cap 4` for the 989-integer equation. To rebuild the source parents:

```sh
python3 direct/code/bootstrap_builder.py --output /tmp/parent781
python3 direct/code/bootstrap_builder.py --radius linear --output /tmp/parent783
```

To compile the PDF with a conventional LaTeX installation:

```sh
sh build_report.sh
```

The equation format stores a term as `[coefficient, variable_indices]`.
Indices are zero-based; repetitions denote powers and `[]` denotes a constant.
The single polynomial is the sum of the squared residual rows. The separate
expanded file is checked term by term against that definition.

## Proof and review scope

The new transformations have complete ordinary mathematical proofs, formalizable
in ZFC, in the report and component proof files. Their Con(ZFC) interpretation
composes with explicitly identified inherited source/compiler/calibration proofs.
The archive retains the named C222-to-ZF and ZF-to-ZFC Lean interfaces and the
ordinary arithmetic proofs, but does not rebuild their entire transitive formal
development or supply a new end-to-end Lean/Rocq theorem or object-language ZFC
derivation. Exact finite artifact checks are distinguished from universal proofs.

Independent AI-assisted reviews cover the factorial lemma and its call order,
the nine-variable majorant and semantic transplant, and the integer sign rules
and actual proof schedule. Their precise scopes and hashes are included.
No worldwide novelty certification, absolute simplicity minimum, proof of
Con(ZFC), or proof that an actual solution exists is claimed.

## Source and licensing

Comparison snapshot: `8f8fac484b976ba0ab75fd173282e838ca5a3b85` of
`VladimirReshetnikov/ProveIt`. The earlier calibration commit and exact inherited
files are separately pinned in the component ledgers. Historical notices inside
`upstream/` describe their original submissions; they are retained for attribution.

New material is supplied under the included **MIT No Attribution** license,
consistent with the target repository. Inherited licenses, notices, and source
attribution are preserved. This package is prepared for incorporation; it does
not modify or publish to the remote repository.
