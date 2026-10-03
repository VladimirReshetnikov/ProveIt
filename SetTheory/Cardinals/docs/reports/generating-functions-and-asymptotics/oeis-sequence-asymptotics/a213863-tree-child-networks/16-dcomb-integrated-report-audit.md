# Integrated TeX audit of fixed combining degree asymptotics

Date: 2 October 2026

## Verdict

The integrated TeX preserves the mathematical content approved in the earlier detailed audit and incorporates both requested precision repairs. No new substantive mathematical gap was found. It supports positive amplitudes and every finite order for diagonal and maximal-reticulation counts at each fixed d ≥ 2, and only a leading equivalent for total counts at d ≥ 3. The source is suitable for the producer's separate rendering and visual review. This audit does not certify visual layout, numerical amplitude digits, universal novelty, or external peer-review status.

Reviewed file: `/workspace/shared/d-combining-extension/release/d-combining-asymptotics.tex`

Pinned SHA-256: `70a1aab9a44bd61a7879e9f64342595c7a4e1438e7798e4dc908dc63ad7f999f`

## Repairs verified

The right boundary is now q[n+1,n+1]=q[n+1,n]=sum b[n,j]=a[n], with n≥1 stated for the corresponding A identity. Thus there is no reference to an undefined q entry beyond its own row. Section 7 now explicitly restricts the approximate solution Z_N to j congruent to N modulo 2, setting the other entries to zero. The parity sample norm and common limiting projection therefore use the correct factor 1/2.

The integrated text also specifies interpolation values epsilon^(-1/2)v_j and explains the artificial-endpoint gauge definition. These changes remove the normalization ambiguities identified in the first review.

## Constants and finite coefficients

The exact product coefficient, c, eta, rho, and B agree with the audited draft. The frozen cubic correction remains -2 eta, while the nonautonomous scalar cubic coefficient is -eta-1/6. The elementary N=1 check added to the TeX is correct: p_1(1)=(d-1)!/(d+1)^(d-1)=1/Lambda, yielding v_1=e_1/sqrt(Lambda).

The displayed d=3 logarithmic coefficients are B²/162, 11B/324, and 4B³/6561-3/16. These agree with the exact symbolic replay in the audit archive after N=2n. The binary comparison coefficients also agree. They remain logarithmic coefficients; the text does not misidentify them as coefficients of the unlogged correction factor.

## Source and leaf indices

The partial-sum A recurrence, A[n,n]=a[n], and maximal identity T[n,n-1]=n!a[n-1] are preserved. Changing the source leaf variable to v=n+1 gives alpha+d-1=rho. Conversely, the exact leaf shift changes the maximal amplitude to gamma_d/Gamma and the polynomial power to alpha. The finite Taylor expansion of the remaining shifted factors is legitimate.

The integrated report keeps the total-count use of the primary source restricted to total/maximal tending to one for d≥3. It does not import the binary total-count identity or infer finite-order total-count corrections from that ratio.

## Analytic transfer

The global confinement and form argument, parity singular gap, finite quasimode remainder, moving Perron-vector estimates, summable adjoint projection drift, Catalan endpoint smoothing, lower-bound contradiction proving positive amplitude, and zero-limit bootstrap all retain the logic and rates checked in the detailed audit. No reliance on a full spectral-radius gap or a uniformly bounded inverse shrinking gap was introduced.

The coefficient-field argument uses the natural n-scaled coordinate and still yields rational polynomial dependence on B for fixed d. The theorem claims only finite Poincare expansions, not convergence of the infinite series.

## Inversion and integer scope

The Lambert-W seed and first correction have the same correct factorial-power and amplitude choices as the audited draft. The smooth model is explicitly a finite truncation; no derivative of an unknown discrete asymptotic remainder is taken. The root uncertainty O(x^(-R/3)/log x) follows from the explicit model derivative.

The newly explicit eventual-monotonicity bound is correct: using the A recurrence at k=n-1 gives a_n ≥ binom((d+1)n-2,d-1)a_(n-1). It exceeds a_(n-1) for sufficiently large n, and the factorial leaf factor preserves eventual strict increase for maximal counts. The report requires neighboring-integer bracketing and explicitly states that amplitude and remainder enclosures are absent. It therefore makes no unjustified certified numerical threshold or unconditional ceiling claim.

## Record

This integrated review compared all 406 lines of TeX with the earlier audited argument and checked the displayed coefficient and boundary expressions against the existing exact replay outputs. The broad novelty and dissertation statements were not newly re-investigated in this integration pass. Visual QA remains a separate production check. The accompanying integrated hash receipt identifies this exact source version; later changes require rechecking or an updated receipt.
