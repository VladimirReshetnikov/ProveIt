# Conditional population from the rank window

This source draft adapts the promoted generic half-binomial population argument. It replaces the positive old-chart alpha and its specific rank formula by the explicit strict window `3*q<R`; from `q=exp h` it obtains the lower bound on `R` used by the same argument. It retains `X=exp R`, `q^3 | Y`, the aligned first index and the two same-witness ordinate equations, as well as their positivity and index conditions.

The [independent source review](../../reviews/trace74-population-window-draft-independent/README.md) found the algebraic substitution sound. The [guarded check and independent result audit](../trace74-population-window-rebuild/README.md) passed against the captured provider union. The theorem does not derive power, index alignment, ordinates or any population bound from a 74 graph zero, and it does not assume the target sum guard.
