# Independent audit of the effective fixed-gap and gap-eight proof

Reviewed file: `sections/02_gap_reconstruction.tex` (authoring fragment `gap_notes.tex`), source revision
`03112a7d3b91efdd3c00b6e595cf0ffa4694d2dc`.
Audit date: 2026-10-12.

## Verdict

No mathematical flaw was found in the reviewed analytic threshold chain.
This is an independent internal audit, not external peer review, interval
certification, or proof-assistant verification. The finite-field program
was only lightly inspected during this audit; its separate exact replay
and rational bridge checks provide the computational evidence.

## Independently rederived or checked

1. The exact normalized real log-Gamma expression for `L_m(x)`.
2. Its remainder coefficients `13m/24` and `16m/45`, hence the
   `259m/360 < 3m/4` bound for `x >= 2`.
3. The DLMF 5.11(ii) logarithmic Stirling remainder factor:
   the first omitted term is bounded by `sec(arg(z)/2)^4 <= 4`,
   giving `1/(90 |z|^3)` after the `1/(12z)` term.
4. The normalized sinh and tanh errors, compact-density estimates,
   and combination with the Gamma density error.
5. The shift from `y=x+i/2` to the positive real ray; the pole at
   `i/2` remains outside the shifted strip with real part at least `2m`.
6. The general Taylor bound for `(1-i/(2y))^(-m)` and the sharper
   fourth-power coefficient `376/81 < 5`.
7. Both general compact/Laplace ratios and the factorial lower bound
   with `k=N-m-2`, including persistence of the elementary power bound.
8. The exact Gamma ratios for odd and even modes, the even-column row
   correction, and the resulting `E_m/b` estimate.
9. The product of phase signs `(-1)^floor(m^2/4)` and its interaction
   with the reversed-Vandermonde sign and initial determinant sign.
10. Every displayed general threshold `B(m)` for `m=1,...,6`, recomputed
    with exact rational determinants and permanents. The values match:
    `8192, 18432, 32768, 51200, 635656, 16146233`.
11. The specialized `m=4`, `b>=8192` bound, including both even-column
    row corrections: `6/(2b-2)+104/(2b-3) < 110/(2b-3) < 1/128`.
12. The exact determinant perturbation margin
    `357064449025/1231171548132409344 > 0`.
13. The polynomial subtraction exponent in the gap-eight ordinary
    sum: the retained nonnegative powers are `x^8,x^6,x^4,x^2,1`,
    and the remaining summand is `O(x^-2)`.
14. The Cramer cofactor factor `4b` and the centered-difference factor
    `4b-1` in the leading coefficient formula, with the initial case
    separately covered by its exact computation.

Two missing-backslash TeX typos were reported to the authoring agent,
who confirmed correction. They did not alter the underlying formulas.

Primary remainder source personally inspected:
https://dlmf.nist.gov/5.11, subsection (ii), first paragraph.
