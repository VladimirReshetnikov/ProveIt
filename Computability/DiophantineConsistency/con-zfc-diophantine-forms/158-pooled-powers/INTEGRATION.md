# Suggested ProveIt integration

This package is prepared for review and incorporation. It does not modify
or publish anything in the upstream repository.

## Suggested incoming entry

`ConZFC_Pooled_Powers_2026-10-25.zip` — **225 unrestricted integers,
degree 4, 162 quadratic residuals, 7,867 collected monomials, coefficient
height 128,446.** Direct square-shell/C222 refutation encoding. Two
quadratic equations pool all power requests at a common base using the
unchanged Pell frame; groups of eleven and three save twelve coordinates.
Cofinal strict ranges, a linear beta base, and exact auxiliary-coordinate
changes save eight more. The 245-variable Joint Norm construction is the
immediate parent. Variable and residual counts improve; support increases.
The archive includes ordinary proofs, full literal equation and expansion,
reproducible stage certificates, independent finite verification, LaTeX,
PDF, retained parent sources, and the syntax-recoding proof supplement.
No new end-to-end proof-assistant verification or global minimality claim.

## Review order

1. Read the main theorem, the quadratic pooling theorem, and the signed
   bootstrap in `report/report.pdf`.
2. Check the cofinal completeness arguments for strict local ranges and
   `y=V-1`; these are semantic changes and are not merely invertible
   coordinate eliminations.
3. Run `python3 -B verify.py --rebuild` and `python3 -B -O verify.py`.
4. Run `python3 -B code/check_report.py` to authenticate the printed equation.
5. Inspect the square-shell/C222 bridge and the inherited logical interfaces.
6. Preserve the new equation's identity and notices if relocating files.

## Exact endpoint

```text
variables: 225 (all unrestricted integers; all occur)
quadratic residuals: 162
degree: 4
collected monomials: 7867
coefficient height: 128446
maximum residual coefficient: 256
equation SHA-256:
fee84c408828aba3e7ceebe9a37f58509327063aa7fd078fd49c80adf3af4e56
```

Suggested title: **Pooling exact power certificates**.
The core reusable theorem is the two-equation aggregate plus the
squared-frame exactness argument. The 225-variable polynomial is its
fully instantiated consistency-equation application.

## Deliberate limits

The optional 224-coordinate affine experiment was not adopted: it substantially
increased coefficient height. It is not included as a second claimed endpoint.
The package's principal metric is fewer variables at degree four with the
parent coefficient height preserved. Future work can optimize the support
or formalize the small pooling module before altering the inherited logical
calibration.
