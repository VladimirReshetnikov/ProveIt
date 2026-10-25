# Positive Pell comparison centers: direct natural quartics for Con(ZFC)

The principal fixed polynomial has **221 nonnegative integer unknowns, degree
4, 172 quadratic residuals, 9,536 collected monomials, and coefficient height
83,954,186**. Its sparse companion has **222 unknowns, 173 residuals, 6,821
monomials, and height 83,954,028**, also at degree four.

Each polynomial is exactly the sum of the squares of every residual in its
`equations/natural221/equation.json` or `equations/natural222/equation.json`.
All coefficients of the collected polynomial are supplied in the adjacent
`expanded_polynomial.json`. A term `[c,[i,j,j]]` denotes `c*x_i*x_j*x_j`;
an empty list denotes the constant monomial. Coordinate indices start at zero.

By the ordinary proof in `PROOF.md`, composed with the explicitly retained
C222/ZF/ZFC calibration, ZFC proves that the equation has no natural zero
if and only if Con(ZFC). The natural domain means `{0,1,2,...}`. No variable
exponent, factorial, binomial, unbounded residual list or unspecified
universal-polynomial parameter occurs in the final equations.

## Main additional lemma

For the principal Pell ordinate Y, auxiliary norm pair U,V, and base A, choose

    V = 2*Y^2*(e+1),
    C = A+(4*Y+1-A)*U^2.

The auxiliary norm forces `U^2 = 1 mod 4Y`, so this one polynomial center
automatically supplies `C = A mod U` and `C = 1 mod 4Y`. The natural domain
of C and the norm imply C>=A, permitting restoration of the two old natural
congruence quotients. Conversely, canonical Pell witnesses supply a positive
center with new auxiliary pairs. This removes the two freely chosen
comparison parameters. The final implementation needs one new square wire
and saves one net coordinate after exact contraction.

Four equal-denominator remainder pools are composed with the inherited
self-sized radix `(N*S)^x`; a separate ordinary proof supplies the extra
completeness budget. A factorial-digit output bound is deleted only after
proving it from the exact-power bootstrap, before any factorial/binomial
interpretation. The one-row semantic anchor and K=x alignment are inherited.

Against the strongest inspected direct natural quartics in `graph_digits`,
the principal endpoint changes 226/175/10,314/87,839,583 to
221/172/9,536/83,954,186 (variables/rows/terms/height). The sparse comparison
changes 227/176/7,905/87,839,583 to 222/173/6,821/83,954,028. Each is a strict
improvement in all four displayed metrics at unchanged degree and domain.
These are direct-C222 comparisons, not global variable-count records.

## Reproduce

Python 3.10 or later; standard library only. No internet, prior ZIP or external
repository checkout is needed.

```sh
python3 -B verify.py --rebuild
python3 -B -O verify.py --rebuild
python3 -B render.py --check
```

The verifier independently matches every changed and unchanged raw row,
authenticates 123 inherited files, replays every rational-square nonnegativity
certificate and monic substitution, recomputes every final coefficient, rejects
seven deliberate corruptions, and checks eight exact local Pell witness
examples. Rebuilding compares all twelve generated JSON files byte for byte.
The TeX transcription is parsed back to the complete literal residual list.
Receipts of actual runs are in `verification/`.

To construct another output directory:

```sh
python3 -B build.py --output /path/to/empty-directory
```

To evaluate a JSON array of candidate coordinates:

```sh
python3 -B evaluate.py coordinates.json --variables 221
```

Exact evaluation is not a decision procedure for solvability.

## Proof and provenance boundary

The comparison repository is pinned to
`e0c98c629bf10d30b695884f6b1d2ab361bdf513`. The incoming cofinal-anchor source,
complete raw graph, inherited arithmetic sources, logical interface files,
portable producer closure, notices and original license are retained under
`inherited/`. `PROVENANCE.json` binds their exact bytes and the source archive.

The positive comparison center and new composition receive an ordinary
mathematical proof. Finite checks verify literal algebra and artifact binding;
they do not replace that proof or decide consistency. This contribution does
not claim a newly completed end-to-end Lean/Rocq/object-language ZFC proof,
global optimality, or literature-wide priority. New material was prepared
with AI assistance. Inherited files retain their original notices.
