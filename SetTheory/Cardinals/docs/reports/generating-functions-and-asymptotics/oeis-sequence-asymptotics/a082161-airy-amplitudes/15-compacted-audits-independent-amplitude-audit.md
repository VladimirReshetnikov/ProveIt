# Independent audit of the compacted signed-delay argument

Audited file: `amplitude-allorders-candidate.md`, as read on 2 October 2026.

## Verdict

**The new compacted-delay argument passes this audit, conditional on the quantitative relaxed-Jacobi lemmas stated in its Section 2.** I inspected those lemmas in the supplied neighboring relaxed proof for consistency with how they are used; this report does not replace their separate independent audit. I found no missing compacted-specific spectral estimate, hidden positivity assumption for the signed propagator, or endpoint-smoothing assumption.

One precise clarification is required in Section 11: for the cube-root grading argument, define `phi_a` for general complex a as the unique entire initial-value solution

    phi_a''(x)=2(x+a)phi_a(x), phi_a(0)=0, phi_a'(0)=1.

At the physical `a=2^(-1/3)z`, this is `F/F'(0)`. For `omega*a`, it must not be interpreted as the identical decaying-Ai formula with a replaced by omega*a, because Ai(omega*z) does not generally vanish. The initial-value definition gives the claimed covariance exactly and repairs the coefficient-field wording. No other mathematical change is required by this audit.

The proof remains a proposed mathematical result, rather than a published theorem. Exact finite tables and formal matching alone would not establish it; the convergence and stability argument below is the reason the candidate passes.

## Exact recurrence, gauge and support

I independently derived the scalar delay from the positive H-decorated-path automaton. Before conjugation its coefficient is

    beta_(N,j)=2(N-j-2)/((N+j)(N+j-2)).

The delayed source is `(N-3,j-1)`, so it is used only for `j>=1`, `j<=N-2`, and valid parity. At j=N-2 the coefficient is zero. At j=0 the source is outside the half-line and the contribution is zero. The formal negative coefficient at j=N is correctly excluded. Thus the support convention in Section 3 is essential and is stated correctly.

Direct cancellation of gamma factors gives exactly

    [D_(N-3)(j-1)/D_N(j)]^2
      = (N-j+1)(N-j)(N+j)(N+j-1)(N+j-2)(N+j-3)
        / ((N+1)N^2(N-1)^2(N-2)).

On the physical support, this ratio is bounded uniformly. The rational beta factor is bounded by C/N, hence `||L_N||<=C/N` globally, without any tail assumption.

For `j<=2sqrt(N)`, expansion gives `ell_(N,j)=2/N+O((j+1)/N^2)`. Applying this to cutoff Airy samples with `||j*g||=O(N^(1/3))` yields the claimed O(N^(-5/3)) coefficient error. The O(N^(-4/3)) eigenvector approximation errors are multiplied by O(1/N), hence are smaller. The unilateral shift differs from the new ground profile by O(N^(-1/3)); its zero at the left endpoint causes no larger error. The shifted parity is correct because N-3 followed by a one-site shift has parity N.

## Scalar drift cancellation

The product ratio `R_(N-3)/R_N=1/8+O(N^(-2/3))` follows from three eigenvalue factors and the slowly varying N^(-1/4) factor. Consequently

    B_N g_(N-3) = (1/(4N))g_N + O_l2(N^(-4/3)).

Together with `eta_N=1+1/(4N)+O(N^-2)` and `t_N=1+O(N^(-4/3))`, this proves the stated summable scalar drift remainder. An adjoint-ground estimate for B_N is not needed in this argument.

## Finite-memory estimates

For the first lemma, put `v_N=K N^(2/3-r)`. Then

    v_N -(1-cN^(-2/3))v_(N-1) - C N^-1 v_(N-3)
      = K c N^-r + O(K N^(2/3-r-1)).

The error is smaller by N^(-1/3), regardless of the sign of `2/3-r`. For large starting N and then large K this dominates the forcing. This supplies the claimed barrier for every fixed real r and handles the finite initial triple. The second lemma follows by the same induction, or by repeatedly substituting the polynomial bound. It does not leave a persistent delayed mode unaccounted for.

## Initial amplitude convergence

The common positive gauge preserves `0<=v_compacted<=v_relaxed` componentwise. The relaxed normalized evolution has norm at most one, so `||u_N||<=N^(1/4)` follows without assuming contractivity of the compacted evolution.

The transverse forcing is initially O(N^(-3/4)): both the scalar-profile drift and the entire delayed vector are at most this size. The gap N^(-2/3) therefore gives `||w_N||=O(N^(-1/12))`.

In the projected recurrence the delayed cross-term is bounded by `||B_N||*||w_(N-3)||=O(N^(-13/12))`. The one-step cross uses the stated relaxed adjoint-ground estimate and has the same bound. Multiplying the scalar drift O(N^(-4/3)) by A=O(N^(1/4)) also gives O(N^(-13/12)). The finite-memory scalar difference lemma hence makes the increments summable.

The identity for scalar increments has the correct sign:

    delta_N = b_N(delta_(N-1)+delta_(N-2))
              +(eta_N t_N-1-b_N)A_(N-1)+xi_N.

After A becomes bounded, repeating the transverse estimate and difference estimate gives `w_N=O(N^(-1/3))` and `A_N-A_infinity=O(N^(-1/3))`. No endpoint conclusion is improperly drawn at this stage.

## Arbitrary formal order and uniform residuals

At formal degree m, the newly introduced profile is G_(m-2). Its delayed occurrence is multiplied by beta starting at degree three, so it enters too late to alter the leading profile inversion. The same is true of a newly introduced scalar in the two previous ratio factors. Thus the claimed Airy polynomial recursion is triangular.

The polynomial operator

    Q -> -Q'''/2 + 4(x+a)Q' + 2Q

has diagonal coefficients 4j+2, all nonzero. The new scalar shifts Q by a constant, enforcing Q(0)=0; the remaining constant in P enforces P(0)+Q'(0)=0. These are exactly the value and derivative boundary normalizations because F(0)=0 and F'(0) is nonzero.

The cutoff residual argument is sufficient globally. On `j<=2sqrt(N)`, `D_N^-1` is bounded by a fixed constant since its logarithm is O(j^2/N). Coefficient denominators stay bounded away from zero. Taylor remainders are bounded by an arbitrarily high power of epsilon times a fixed polynomial-Airy envelope. Time-dilation shifts stay O(epsilon) on this support, so the same envelope controls their derivatives. Cutoff changes and shifts occur only where the Airy factor is exponentially small. At the left boundary all fictitious samples are exactly zero. The upper physical boundary is outside the cutoff for large N. Restricting each vector to its parity merely changes the leading Riemann-sum factor to 1/2.

It is enough to know only the leading asymptotic of P_N here: the original approximate recurrence is divided by the exact R_N, so no unproved all-orders expansion of the relaxed spectral product is being used.

## Zero-limit bootstrap and endpoint

Given alpha=O(N^-q), the transverse finite-memory estimate gives

    W=O(N^(-q-1/3)+N^(2/3-p)).

The scalar difference forcing is then

    O(N^(-q-4/3)+N^-p),

because the extra `N^-1*W` residual contribution `N^(-p-1/3)` is smaller. The increments are summable, and the imposed zero limit justifies summing forward to infinity, yielding

    alpha=O(N^(-q-1/3)+N^(1-p)).

This improves q by 1/3 until the residual floor p-1 is reached. Applying the bound to a sum of powers is covered by the finite-memory lemma. Therefore `||E_N||=O(N^(1-p))` follows for any prescribed p>1.

Point evaluation loses only the factor N^(1/2) relative to the normalized ground endpoint. Since p can be chosen arbitrarily large, this yields all finite algebraic endpoint orders. If A_infinity=0, the same homogeneous bootstrap makes the endpoint o(N^(-1/2)), contradicting the cited compacted lower Theta bound. The strict positivity argument is not circular.

The amplitude conversion checks exactly:

    gamma_c = 2^(3/4) C F'(0) = 2^(7/4) kappa A_infinity.

All truncations have the same leading normalization and the same q_0, so this is a common amplitude, rather than an order-dependent collection of constants.

## Independent symbolic check

`audit_compacted_coefficients.py` performs a separate direct linear solve for the unknown P,Q,s coefficients. It neither imports the proposed coefficient program nor uses its triangular inversion routine. Its results are recorded in `audit_compacted_coefficients_results.json`.

It independently confirms

    s_2=a,
    s_3=13/12,
    s_4=29a^2/270,
    s_5=-11a/324,
    s_6=(2054835-140528a^3)/1360800.

The normalized endpoint series through epsilon^3 is

    1+(a/3)epsilon^2+(13/12)epsilon^3.

After converting N=2n and a=2^(-1/3)z, the three logarithmic correction coefficients are exactly

    53z^2/90,
    271z/216,
    393/1120-1304z^3/42525.

The corrected initial-value interpretation of phi_a gives `phi_(omega*a)(omega*x)=omega*phi_a(x)`. The formal recurrence is invariant under simultaneous multiplication of a,epsilon,x by omega. Hence order-k monomials a^r satisfy r+k divisible by three, and the converted coefficients indeed belong to Q[z].

## Final revision verification

The Section 11 initial-value clarification has now been made and checked. The candidate revision with SHA-256

    e0bd7dd95a9dff72247f366d343eca56f25154d83734899c5ec0b60ef96df937

passes this audit of the compacted extension. Its self-contained shared-lemma file has SHA-256

    8dfa65e23d19c7c6f93b6e64bc9f236ae538bf14850d07c85a3fb356775a56dc.

The independent symbolic coefficients printed in the revised candidate match the audit calculation exactly. The earlier Section 11 clarification is resolved.
