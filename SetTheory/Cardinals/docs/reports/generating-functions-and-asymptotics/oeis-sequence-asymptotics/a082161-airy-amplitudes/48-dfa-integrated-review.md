# Independent integrated mathematical review

Date: 2 October 2026.

Reviewed standalone source: `dfa-finite-languages.tex`.
Initial reviewed SHA-256: `eb7e2a67990d52d090eb8998ba93087cae6acb823847648e1e2c087a77fe1592`.

## Verdict

The integrated mathematical argument passes. One harmless standalone-definition clarification was requested: explicitly set D_0(0)=1, v_0^(r)=delta_0 and P_0=1, since the gauge was introduced for N>=1 but the initial contraction is used from N=0. This does not change a recurrence, estimate or coefficient. A final-source verification below will pin the accepted revision after this and any layout-only edits.

This review covers the mathematical manuscript. It does not certify decimal digits of the amplitude, universal novelty, the runtime of every release script, or visual PDF quality. Those matters are appropriately distinguished from the theorem in the article.

## Exact model and initial values

The source correctly retains the auxiliary b(-1,0)=1 and identifies A331120 with n transient states plus one rejecting sink. The explicit sentence preserving this auxiliary value resolves its precedence over the zero-outside-triangle convention. Uniform normalization c=b/2^m is correct at m=0 and m=1.

The positive renewal proposition reproduces b(n,1)=2^n-1; its convolution kernel is [2-(m+1)t^2]/[1-(m+1)t] and has the displayed positive coefficients. The triangular cutoff is explicit and essential. The formulas recover the signed recurrence and b_n=A(n,n). Positivity and induction justify 0<=c<=r without assuming positivity of the signed propagator.

The exact physical seeds are correct:

    e_0(0)=1, e_1(1)=1, e_2(0)=e_2(2)=1/2.

In particular e_2(0) is 1/2, not 1, because of the negative-index auxiliary datum. The ungauged physical recurrence starts at N=3, and then uses only physical N-3 vectors. At N=3,j=1 it gives 1/2+1/2-1/4=3/4, agreeing with c(2,1)/2!. The upper seed propagation gives e_3(3)=1/6. The delay is correctly retained for m=1, omitted for m=0, and zero for j=0. Its valid source interval is 1<=j<=N-2.

## Parameter replacements and normalization

Every consequential DFA replacement was checked against the direct derivation and the earlier audit:

- Delay coefficient (N-j)/[(N+j)(N+j-2)] and its unchanged factorial gauge ratio
- Global delay norm O(N^-1), leading coefficient 1/N, and drift 1/(8N)
- R_N=P_N N^-1/8 and eta_N=(N/(N-1))^1/8
- Initial domination N^1/8, transverse bound N^-5/24 and summable increment bound N^-29/24
- Scalar log-amplitude exponent 29/24
- H_N/R_N asymptotic kappa^-1 N^-1/6 and normalized endpoint N^-1/2
- Conversion b_n=2^n n! e_(2n,0), final exponential 8^n and polynomial power 7/8
- Common amplitude gamma=2^7/8 C_*F'(0)=2^15/8 kappa A_infinity

The norm-bootstrap and its forward-tail summation use a known zero limiting projection. No endpoint smoothing, contraction of a signed operator, or additional slow-mode assumption has been inserted. For remainder order M the condition p>=3/2+(M+1)/3 is sufficient. Published positivity is invoked only after convergence and arbitrary-order error control, so the strict-amplitude argument is not circular.

## Explicit constants and coefficient field

All displayed scalar ratio coefficients, finite logarithmic amplitude coefficients, endpoint coefficients, and final logarithmic and relative corrections agree with the independent exact polynomial-linear-system computation. In particular:

    s_3=29/24, s_5=-103a/648,
    s_6=(5341815-562112a^3)/5443200,
    h_2=551a/216,
    h_3=2371/6720-5216a^3/42525.

The final logarithmic coefficients are 53z^2/90, 623z/432, and 3497/4480-1304z^3/42525. Exponentiating gives exactly the three displayed relative coefficients. The initial-value interpretation for complex Airy parameter is correctly retained; the grading argument establishes Q[z] after conversion from N to n.

## Self-contained shared appendix

The entire shared appendix was reread and compared against the independently reviewed compacted integrated baseline. Apart from changing 'compacted theorem' to 'DFA theorem' in its introduction, it is identical. It contains the exact symmetrization, positive top eigenvector and contraction, coercive quadratic form, compactness/min-max Airy limit, parity singular gap, explicit finite quasimode and norm residual, eigenvector approximation, overlap/adjoint estimates, Airy endpoint identity, and convergent spectral-product normalization.

The use of parity removes the negative extreme eigenvalue. The transverse inequality for every preceding-parity y is justified by projecting S_N away from its top incoming singular direction before bounding Q_N; it does not require y perpendicular to that direction. The needed quantitative profile and diagonal-defect estimates are proved within the appendix. No relaxed all-orders amplitude theorem or external unpublished lemma remains as a mathematical dependency of the integrated source.

The elementary Airy ODE/decay facts are cited to the standard DLMF reference. Standard compactness and min-max principles are used explicitly rather than hidden behind a claimed special spectral theorem.

## Inverse and scope

The selected smooth inverse is an explicitly defined model, not a continuation of the integer sequence. Stirling contributes (11/8)log x, as displayed. With w=W((8/e)Y), X=Y/w, the correction denominator 1+w equals log(8X). The first inverse remainder O(X^-1/3/log X) is valid; the differentiated stretched term and factorial-core quadratic term give smaller index errors.

The all-orders estimate is now explicitly written at the discrete samples:

    x_M(log b_n)-n=O_M(n^(-(M+1)/3)/log n).

The source distinguishes this from arbitrary discrete thresholds and from numerical solution error for a fixed model. Eventual monotonicity follows from the leading asymptotic, b_(n+1)/b_n~8n. No certified finite threshold algorithm is claimed from an unspecified big-O constant. The parameter-family extension remains a conjectural direction requiring an additional lower bound; no unsupported family theorem appears.

## Final source verification

The initialization clarification has been added and checked at the start of Section 3: D_0(0)=P_0=1 and v_0^(r)=delta_0. The additional reported layout changes concern the table of contents only.

**Approved mathematical source SHA-256:** `4227ead32b406c56457e65b50044ce1df65ee5a1a82403bada55caf1b0ffacaa`.

This exact source passes the integrated mathematical review. The previously noted initialization clarification is resolved.
