# A structural route toward the conjectural 2/3 logarithmic-square coefficient

This file is deliberately a **formal research route, not a theorem**. The padded-barrier theorem proves only an O(log² n) coefficient upper bound. The calculation below explains why the numerical candidate 2/3 is mathematically natural, and identifies the estimates still missing.

## An exact frozen-kernel identity

Use the notation of `padded-barrier-proof.md`. After changing the integration variable y to weighted rank r'=h(y)/D, the frozen positive kernel normalized by its eigenvalue λ becomes

    P_q(r,dr') = [q/(1−e^(−q))]
                 exp(−q((r'−r) mod 1)) dr'.

This equality is exact for the continuous frozen kernel: on duplicate labels dy=D dr', while on new labels dy=D dr'/R; the relation e^p/R=e^(q−p) makes both pieces agree. It is a convolution kernel on the unit circle, with uniform stationary density. Its Fourier multipliers are q/(q−2πij), up to the chosen Fourier sign convention. On smooth zero-mean periodic functions this gives the exact identity (P_q−I)^(-1)=q ∂_r^(-1)−I for the corresponding orientation.

The actual discrete operator also changes s,u and hence D and the rank map. The frozen convolution identity is not an exact representation of that evolving chain.

## Formal first transport correction

Let z=s/D and take q large with D much larger than a suitable polynomial in q, away initially from the rank-wrap and type-interface boundary layers. As R→2, Euler–Maclaurin and the first shifted-rank correction suggest

    V/b := (T_op ψ/ψ − ∂_t log ψ)/b = q f(r,z)+O(1+q²/D),

with the leading bulk function

    f(r,z)=1/4+r/2  for r<z,
           r/2      for r>z.

The 1/4 term is the half-endpoint quadrature correction for a duplicate ascent. For a new ascent, its quadrature term q/2 is canceled in part by the rank shift −q(1−r)/2. For a duplicate ascent the shifted rank contributes +qr/2. This is a bulk expansion; it is not asserted uniformly through r≈0, r≈1 or r≈z.

Averaging over the exact frozen stationary rank gives

    integral_0^1 f(r,z)dr=(1+z)/4.

Under the same asymptotic Doob dynamics, duplicate labels have stationary fraction z, new labels fraction 1−z, and mostly ascending transitions increase D by 1. After rank averaging (not pointwise), this gives

    L_q z / b ≈ (1−3z)/2.

The stable composition is z=1/3. More usefully, the correction exp(qz/6) cancels the state-dependent part at leading order:

    q(1+z)/4 + q(1−3z)/12 = q/3.

This suggests a global scalar factor exp(q²/6). A rank Poisson correction for the mean-zero part of f should have logarithmic size of order q²/D, because the frozen convolution has forward drift of order 1/q per jump and jump rate of order bD.

## Why this suggests 2/3

The characteristic endpoint satisfies T−t(q)~sqrt(2)(q+2)e^(−q/2). A lognormal singularity with logF~q²/6 has its coefficient saddle at q~2log n, and therefore suggests

    log(a_n/(n! μ^n)) ~ (2/3)(log n)².

This is also the target selected by the separately documented exact/floating coefficient diagnostics. Agreement between formal transport and finite-range fits is not a proof.

## Precise missing steps

1. A uniform evolving-state expansion replacing the bulk formula for V, including rank wrapping, the duplicate/new interface and the q-dependent R. A frozen stationary average by itself does not establish the potential accumulated by the true chain.
2. Quantitative averaging of the exponential Feynman–Kac weight, not just convergence of ordinary rank/composition expectations. The potential can bias atypical trajectories.
3. Control of the fixed-root boundary layer. At x0 the original-ψ transformed jump rate divided by b is of order Q exp(−Q/6); the root is nearly trapped on the q-time scale. Therefore an ordinary typical-trajectory argument for fast escape is false. A rare-path or weighted seeding estimate is needed. Once a genuinely large state is reached, the averaged dynamics suggests D grows roughly like exp((Q−q)/2), but this cannot be extrapolated to the fixed root. The existing O(Q²) barriers are not sharp enough to bound this weighted boundary contribution by o(Q²).
4. A coefficientwise transfer theorem. Even proving the real-axis singular estimate for F would not, with positivity alone, give the displayed individual-coefficient equivalent. A local limit estimate, sufficient regularity, or complex saddle analysis is required.

All-orders asymptotics would additionally require the next transport terms, a nonzero finite amplitude, and controlled analytic transfer. None of these are supplied by the new upper theorem.
