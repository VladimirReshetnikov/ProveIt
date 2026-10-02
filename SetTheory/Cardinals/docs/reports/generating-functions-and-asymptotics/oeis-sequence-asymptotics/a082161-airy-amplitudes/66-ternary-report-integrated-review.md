# Integrated review of the ternary Airy amplitude report

Date: 2 October 2026

## Verdict

Approved. The integrated argument is mathematically consistent with the separately audited proofs. It establishes a positive leading amplitude for relaxed ternary trees, an expansion to every fixed finite order for that relaxed sequence, and a positive leading amplitude for the ternary finite-language DFA sequence. The inverse formulas have the stated precision under the specified log-linear interpolation convention. I found no remaining theorem-level discrepancy in the constants, boundary conventions, or transfer of estimates.

The final source explicitly includes the exact normalization `d_i(j)=4^x r_{x,m}/x!` and invariance of each fixed-endpoint bridge measure. This supplies the identification needed when the original completed-run expectation is controlled by transformed-path tail estimates.

This review does not certify any general-arity extension, all-orders DFA expansion, numerical evaluation of the leading amplitudes, or exhaustive novelty claim. It is a mathematical source review. PDF production and visual inspection are separate checks.

Approved final mathematical TeX source: SHA-256 `128f71982c13dc1553801cee6fc85df2bdcce145eb9aeb7f132df8ae71c7bea7`. Review completed at 05:09 UTC on 2 October 2026. The approval covers this source and the stated theorem scope.

## Inputs and comparison method

The full TeX was compared with `amplitude-proof-candidate.md`, `all-orders-reduction.md`, `dfa-ratio-transfer.md`, and `inverse-audit/inverse-verdict.md`. I also read the independent leading-amplitude and singular-form verdicts, the all-orders audit, and the DFA-transfer audit. The scalar/endpoint coefficient output was checked against the displayed coefficients rather than treating agreement of theorem statements alone as sufficient.

I independently checked the source identities, the potentially delicate transitions between sections, and finite exact recurrence calculations. The finite calculations are consistency checks only; the analytic arguments remain necessary for all infinite-range assertions.

## Normalizations and leading constants

The transformed coordinates are `i=x+m`, `j=x-2m`; a horizontal step gains the gauge ratio `4/x`, so its transformed weight is `4(m+1)/x=4(i-j+3)/(2i+j)`. A vertical step has gauge ratio one. Thus the newly stated gauge is correct path by path, and `R_n=(2n)!d_{3n}(0)/16^n` follows exactly.

The critical forward and adjoint harmonics, including the alternating term in the adjoint harmonic, agree with the audited formulas. The fixed weight lies between 1 and 3/2. The critical variance identity, the physical phase restriction, and the use of singular values rather than eigenvalues of the nonnormal transfer are retained.

The column-loss formula includes every physical output of a physical input. There is no extra upper-boundary column loss. The strengthened numerical bound `1-c_i(k) >= (4/9)k/i` is valid. For `k=1`, the loss is `3/(2i+4)` and the inequality follows for the physical cases `i>=2`. For `k>=2`, physicality gives `i>=3`, `alpha_i<=3/2`, `2i+k+1<=3i`, and the increasing adjoint harmonic gives its adjacent ratio at least one. The second loss term is therefore at least `4(k-1)/(9i)`, while the first is at least `4/(9i)`.

The scalar product has power `i^(5/2)`, endpoint sampling contributes `i^(-1/3)`, and hence the transformed endpoint has power `n^(13/6)`. The central-binomial factorial conversion reduces that by 1/2 to `n^(5/3)`. The stretched exponent is `gamma=3*3^(1/3)*a_1`. The DFA multiplication by `2^(n-1)` gives exponential base `27/2` and amplitude `C_B=rho*C_R/2`. None of these constants changed in the integrated rewrite.

The first three relaxed correction coefficients also match the independent scalar/profile output. In particular, the pre-conversion coefficient of epsilon cubed has constant `13057/2520`; restricting to `i=3n` and applying the central-binomial Stirling correction gives `13057/7560-1/8=1514/945`, as displayed in the report. This checks the easiest place to lose the `1/n` correction.

## Singular limit and evolving profile

All of the analytic ingredients needed in the source audits remain present:

1. The nonnegative row/column/variance decomposition supplies the lower bound and tail tightness for the singular forms.
2. Localization is performed before the critical radial identity is applied. Thus the missing moving top edge is not silently restored.
3. The exact trace term `3|u_0|^2/(r+1)` fixes the Dirichlet lower endpoint; the report has not replaced it by a Robin or Neumann convention.
4. Near-zero control and column-loss control rule out loss of mass at either end. Strong norm and inner-product convergence preserve dimensions in the min-max argument.
5. Both loss terms contribute one half of the Airy potential. The singular-form normalization is `18 epsilon^2`, giving eigenvalues `-a_m` and singular values `3(1+a_m epsilon^2+o(epsilon^2))`.
6. The one-channel qualification is explicit. The report does not incorrectly use `a_2` as the second singular level on a direct sum of three channels.
7. The forward profile retains the previous-time dilation. Its contribution to the coefficient of `x f'` produces the correct scalar coefficient `15/2`.
8. The adjoint argument retains exact cancellation of the linear boundary harmonic, including the two exceptional bottom sites. Estimating the weighted terms separately would not suffice, but that mistake was not introduced here.
9. The adjacent-phase norm expansion has three phase-independent coefficients before an absolute `O(epsilon^2)` remainder. This justifies the adjacent-time norm ratio; a bare leading Riemann sum would not.
10. Airy-envelope estimates and the moving cutoff supply uniform weighted residual bounds without logarithmic losses. The cutoff remains far below the physical top.

The compressed contraction follows from overlap with the first right singular vector and the singular gap, not from a false frozen-eigenvector identity. The Lyapunov bound, stable convolution, central convergence, and endpoint loss are retained. The positivity argument uses the published lower bound for precisely the initialized relaxed sequence. It does not assume positivity of a nonnormal spectral projection.

One minor presentation point is that the finite Airy form domain also requires finite potential integral `integral x|F|^2`; the report's displayed integral can equivalently be understood as an extended-valued form on `H^1_0`. This does not affect its argument or spectrum.

## Fixed finite orders and the common amplitude

The formal moving equation has the correct rational coefficient and the exact previous-time variables `epsilon*tau` and `(x+d epsilon)*tau`. The factor of three is handled explicitly before solving the polynomial equation. The polynomial operator has diagonal entries `1,3,...,2d+1`, so its invertibility proves each successive stage, rather than merely extrapolating from finitely many symbolic checks. The new scalar enforces `B(0)=0`; the condition `A(0)=0` fixes the amplitude gauge.

For a requested defect `O(i^(-p))`, with `p>1`, the specified finite truncation order is sufficient. The common-envelope remainder, exact bottom vanishing, top separation, and cutoff discrepancy estimates are all retained. The starting index and constants may depend on the requested fixed order. No uniform claim for growing order is justified or asserted.

The scalar ratio must be matched in logarithms. Its new coefficient is `-r*h_r/3` at order `epsilon^(r+3)`. With one fixed lower limit for the leading product and leading constant one in `H_i`, the prefactor `kappa/N_(I-1)` in `Z_i` is correct. Reversing those constants would change the limiting projection; the integrated report does not reverse them.

The zero-limit error is summed backward in the central direction and forward through the contracted stable direction. Starting at bounded central error is legitimate. The repeated improvement reaches `||E_i||=O(i^(1-p))`; endpoint extraction then gives relative error `O(i^(3/2-p))`. Thus choosing, for example, `p>3/2+(M+1)/3` and sufficiently many scalar/profile terms proves the stated `M`-term remainder. The same raw solution amplitude is used for every truncation. No proof step needed for this common-amplitude conclusion was dropped.

## DFA boundary and positive run representation

The auxiliary value `b_(-1,0)=1` is material and is correctly stated. It gives `b_(2,1)=1` and then `b_(x,1)=2^(x-1)-1` for `x>=2`. Setting that auxiliary value to zero would change the enumeration. The initial counts in the report match the intended sequence.

The run convolution can be made fully explicit as follows, with every completed-run array zero outside its triangular support:

- `a(x,m+1)=sum_(ell>=0) V_m(ell)*a(x-ell,m)`
- `A(x,m+1)=sum_(ell>=0) W_m(ell)*A(x-ell,m)`
- `r_(x,m)=sum_(ell>=0)(m+1)^ell*a(x-ell,m)` and the same relation from `A` to `b`

The last identity appends the final horizontal run. The generating function for `W_m` then recovers the stated signed recurrence. At a diagonal endpoint the last horizontal run has length zero, so the endpoint counts are the completed-run arrays themselves. There are exactly `n-1` factors, corresponding to source levels `1,...,n-1`; the initial arrival at level one supplies no additional factor two.

I independently computed these identities using exact integer arithmetic for every physical coordinate with `x<=24`, and the endpoints through `n=12`. All checks passed, including `R_1,...,R_6 = 1,7,139,5711,408354,45605881` and `B_1,...,B_4 = 1,14,532,42644`.

The infinite product lower bound is correctly indexed from `j=2`; Euler's product gives `P_3=(2*sqrt(2)/pi)sin(pi/sqrt(2))`. The retained-level truncation error is uniformly at most `1/(2M)`.

The high-path repair uses the valid polynomial overhead `C t^(3/2)`, not critical pointwise domination. Backward normalized monotonicity includes the lower boundary and the physical upper support. The bridge comparison, binomial lower-tail estimate, and summation give the displayed power `x^(4/3)` and a summable tail uniform in terminal size.

The delayed-rise conversion has the correct direction: a rise ending at time `i` and source level below `M` has height at least `i-3M`, and the preceding three-step block height is at least `p-3M`. Hence fixed-level defects are uniformly approximable by fixed-time defects. Each fixed-time reweighting is a finite initial vector; later evolution needs no hidden run-length state. The tracking argument applies separately for each fixed time, and its comparison amplitude may be zero. The positive reference amplitude makes the endpoint ratio well-defined. These facts justify both uniform-limit passages and the positive DFA leading amplitude, without giving a DFA all-orders conclusion.

## Inverse interpolation and integer thresholds

The logarithmic prefactor is `8/3`, including one from the two factorials, and the constant is `log(2*pi*C)`. Both sequences' leading equivalents suffice to make consecutive logarithmic increments eventually positive. The Lambert solution and derivative `D=2(w+1)` are correct.

The leading residual after substituting the first correction is `o(1)`. Dividing by the interpolant's local slope gives the stated absolute error `o(1/log n_0)`. The universal continuous correction `-4/3`, the amplitude-dependent correction, and the positive direction of the stretched-exponential inverse correction are correct.

The exact integer statement uses the actual inverse: `nu(y)=ceil x(y)` eventually. The report explicitly declines to round an asymptotic approximation as an exact uniform formula. This distinction has survived the rewrite.

For relaxed all-orders inversion, interpolating the truncated logarithmic model preserves the integer remainder without differentiating the enumeration error. The model-root error is therefore `O(n_0^(-(M+1)/3)/log n_0)`. The separate smooth Newton inverse and its quadratic error estimate are valid. The fractional-part correction has the correct negative sign and scale `1/(n log n)`; its stated remainder is valid even near integer boundaries. The report does not identify the smooth inverse with the actual interpolated inverse at arbitrarily high order. Numerical use of amplitude-dependent corrections still presupposes knowledge or evaluation of `C_R` or `C_B`; no such evaluation is furnished here.

## Attribution and scope

The report consistently attributes the inherited relaxed Theta scale and exact recurrence to the source, while presenting the amplitude and finite-order arguments as additional work. The source's DFA table agrees with the report's initial values; A082162 is separately identified and is not described as the minimal finite-language DFA sequence.

I independently opened the [published paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol302-aofa2024/LIPIcs.AofA.2024.15/LIPIcs.AofA.2024.15.pdf), the [arXiv v1 text](https://arxiv.org/html/2404.08415v1), and [A082162](https://oeis.org/A082162). The published high-path proof does contain the incorrect assertion `U(i,j)<=k-1`; the location is Lemma 15, page 15:12. Its arXiv v1 counterpart is Lemma 14. Thus the report's characterization of a published pointwise error is supported, and the specific version/lemma distinction can be given accurately. The bibliography's conference, volume, article number, and OEIS starting-index convention are correct.

The report's exclusions remain necessary: it evaluates neither positive amplitude, claims neither convergence of the infinite formal series nor uniformity in growing truncation order, and proves neither a general-alphabet theorem nor an all-orders DFA theorem. No pending general-arity or delayed-DFA material was imported into this review.

## Final revision check

The final source was re-read after the precision revisions. It now distinguishes the scalar Lyapunov magnitude from the normalized transfer operator, states the localized radial product-difference inequality with its necessary multiplicative constant, matches the scalar ratios explicitly in logarithms, and gives the strict sufficient choice of `p` for the requested finite-order remainder. It also separates the fixed lower limit in the reference normalization from the order-dependent starting time of high-order estimates.

The exact path gauge and published/preprint lemma numbering are explicit. These revisions preserve the constants and introduce no new proof obligation. No mathematical correction remains open within the reviewed scope. This reviewer did not edit the TeX source.
