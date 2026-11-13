# Independent review of the 88 two-norm gap

On 2026-11-04 an independent reviewer examined the generic
[`Absorb88TwoNormGap.lean`](../../research/ordinary12-absorb88-two-norm-gap-draft/Absorb88TwoNormGap.lean),
the actual graph's
[`Absorb88MainRoot.lean`](../../research/ordinary12-absorb88-main-root-draft/Absorb88MainRoot.lean)
and [`Absorb88GraphGap.lean`](../../research/ordinary12-absorb88-main-root-draft/Absorb88GraphGap.lean),
their stated hypotheses, and the relevant graph and quotient source
definitions. No sign, parameter or strictness error was found in this review.
No fresh Lean run was performed.

For `P = XY² > 0`, the first norm's classification gives
`k = 2 y_n(B)` with `B = 2P − 1`. Here the first two positive ordinates are
`1` and `2(B + 2) = 4P + 2`. Since `eta,zeta > 0` and
`k = eta + zeta`, index zero is impossible; index one forces `k = 2` and
`eta = zeta = 1`. The main ordinate would then be `2Y + 1`, strictly
between the main recurrence's first two positive ordinates `1` and
`2(XY + Y + 2)`. That contradicts the assumed main norm and gives `n ≥ 2`,
hence `k ≥ 8P + 4`. The application concerns the indicated models of IΣ₁;
the classification and monotonicity theorems are inherited dependencies.

The 88 output is definitionally a sum of three squares, so a zero forces its
main residual to vanish in the ordered difference ring. Its main residual
is definitionally the 89 main residual for the same ports and tuple. The
main scale `U = Yq²` is positive from tuple positivity, enabling the stated
square-divisibility quotient. The first root uses positive `beta` and tuple
positivity to justify its own positive scale. The source bindings use the
same `q`, `X`, `Y`, `k`, and `c` in both norms, and the main discriminant
`(a + 1)(a + 3)` equals the graph's `a² + 4a + 3` for
`a = XY + Y`.

The conclusion is a necessary bound on zeros, without any transport-sign
assumption. It does not establish a positive transport, the reverse 88/89
existence implication, an iPRA endpoint, or a graph zero. The author's
recorded Lean checks use captured temporary providers; this review does not
authenticate their complete source, package, or dynamic ancestry.
