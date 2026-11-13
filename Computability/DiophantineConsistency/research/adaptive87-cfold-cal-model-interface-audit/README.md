# All-IΣ₁-model interfaces for the C-fold Cal argument

A generic fact-level route is visible in existing source, but the combination
has **not** been elaborated or checked, and the C-fold graph has not been bound
to its facts. In particular, the standard-integer Cal replay is not itself a
model theorem or an internal iPRA derivation. Several useful clients below are
`.lean.src` proposals, not checked declarations. The source inventory checker
pins their bytes and verifies textual interface markers only.

## Signed facts to natural model facts

Let V be an ordered arithmetic structure modelling IΣ₁. Given natural model
values `q,X,Y,k,R,eta,gamma,f,i,T,u`, define

```
a=X*Y+Y, c=eta+Y*k, H=3+4*a, U=Y*q²,
P=U*(X+a*c)+H*(U*gamma+X*Y*q+R+1), N=H*k,
A=f²*(T*c), B=f²*R+c, Delta=H+a².
```

An appropriate model formulation should use the signed pair `(P,N)` or
`magnitude (P,N)` for the main root and the two natural magnitudes
`absdiff A B`, `absdiff (A+u) B` for the auxiliary roots. Its hypotheses
must provide **one** natural first root tau, `Y=q³*s` with positive s, the
main norm of `(P,N)`, the strong norm, and the auxiliary equality. Do not
replace a signed subtraction by natural truncated subtraction without the
needed inequality or pair proof. This formulation can be stated without a
sign assumption on Bt or any old first-root coordinate.

## Prospective same-witness path

1. `ArithmeticAdaptiveMainOrientation2011.main_parts_positive U X Y k eta
   gamma q R` assumes `0<U`, `8<=Y`, `0<k` and gives `N<P` for the **extra
   `X*Y*q`** carrier above. `DirectMainNorm.oriented_scaled_norm U P N C`
   assumes `0<U`, `N<P` and
   `magnitude(P,N)^2=U²*(1+C)`; it produces a positive natural root d,
   `P=N+U*d`, and `d²=1+C`. Here use `C=Delta*c²`. Derive `8<=Y` from
   positive s and q>=3. No old first-root equality is required by these two
   displayed fact interfaces.
2. Construct `ArithmeticAdaptiveMainCongruence2011.MainCongruence p v`
   directly from this additive balance and `Y=q³*s`. This proposition is a
   natural additive q⁵ balance, not an original zero assertion. Then
   `ArithmeticAdaptiveRankCongruence2011.rank_congruence_of_main p v` yields
   `q⁴ | magnitude (R+1,k)`. It uses the existing all-model
   `ArithmeticAdaptiveFactorThree2011.cancel_factor_three`, which takes
   positive q, `q³|Y`, and `q⁵ | (3+4Y(X+1))*t`; it loses one q factor
   without assuming 3 is invertible. Its v-based rank uses natural `q-F`;
   the explicit gap `F+alpha<q` is needed to identify it with the signed
   graph rank. Alternatively adapt the same factor-three proof directly to
   generic model elements; `MainCongruence p v` fixes port values to embedded
   *standard naturals*, not arbitrary unrelated elements of V.
3. `ArithmeticAdaptiveRankWindow2011.scalar_rank_window q beta MC MF J F
   alpha` requires positive beta/J/F/alpha, `MC<beta`, `MF<2*beta`, the
   q identity and `F+alpha<q`. From its window, the positive first norm and
   q⁴ magnitude divisibility, the **unelaborated**
   `ResidueFirstIndexModelDraft.early_index_of_natural_norm` takes
   `q X Y k R tau s` and produces one n and w, including both first Pell
   coordinates for tau, the early residue, and `k=2*n+4*X*Y²*w`. This
   wrapper deliberately avoids `ArithmeticAdaptiveEarlyIndex2011.Indices`,
   which includes the old first-root term and cannot simply be supplied by a
   C-fold zero. Independently classify the **same oriented d** and c via
   `ArithmeticPellClassification.solution_index` to obtain the main index.
4. Supply these same n,w,d and main index, rank window, positive eta/i/f,
   the strong equation and both auxiliary `absdiff` equations to
   `P72Exact.indices_ordinary`. Its later variable `s` is w; its `y0` is the
   distinct quotient Y/q³. Its conclusion gives `13<=n`, `mainIndex=R` and
   `2*n=R+1`. Association, natural `tsub`, rank representation, both
   absdiffs and all casts need explicit source proofs; the existing theorem
   does not extract them from this graph.
5. The **unelaborated** generic fact lemma
   `ResidueThreeProjectionDraft.q_dvd_threeX q X Y c k R gamma d s w`
   takes positive q,s, `Y=q*(q*q)*s`, the exact-index k equation and the
   additive carrier balance. It concludes `q | 3*X`, not `q | X`. The
   **unelaborated** `Positive84PowerDraft.growth` uses q>=46, that divisibility,
   n>=13, `2*n=R+1`, and the same recurrence coordinates to propose
   `Exp.exp R<Y`. Although this particular source imports 84-specific modules,
   the displayed growth theorem's arguments are generic; extracting or
   rewiring its proof still requires import/provider checking.
6. The **unelaborated** `ResidueQBalanceDraft.q_balance` constructs the
   oriented q-balance using the same s,w. The **unelaborated**
   `Positive84OrientedPowerDraft.power_of_oriented_balance` takes that balance,
   `Y=q³*s`, the same main x/y recurrence coordinates and `Exp.exp R<Y`, and
   proposes `X=Exp.exp R`; it does not cancel 3 modulo H. These generic facts
   do not require compact beta or a Mersenne cancellation theorem.
7. For the final `q²<=X`, no new exponential induction is necessary in
   principle: the scalar inequalities give `2*q<=R` for q>=3; Foundation's
   model `lt_exp`, `exp_even`, and `exp_monotone_le` then give
   `q² <= (Exp.exp q)² = Exp.exp (2*q) <= Exp.exp R`. This is a source-level
   proof plan; its exact casts, associations and imports have not been tested.

## Missing graph, port and provider work

The present C-fold zero must separately supply its four vanishing residuals,
C>0, the first natural root/`Y=q³*s` quotient, the main signed-pair norm, and
strong/auxiliary magnitude equations at **one valuation**. The old
`expressionAt_*` theorems hard-code the pre-fold first-root graph and may not
be applied to the C-fold zero merely because most rows are shared. In
particular `positive_Y_quotient_of_facts` assumes the original `Quotients p v`
with its original first-root pair; the new q³ divisibility needs a fresh
binding/proof or an explicit transferable fact. Nonstandard models require the
same quotient and divisibility operations inside V, not standard integer prime
factorization.

For current2011 ports, `CurrentMasks2011.beta_pos`, `lowPort_lt` and
`highPort_lt` are source interfaces for the beta and mask estimates. The
fourth port is `beta+highPort` once; one must explicitly derive its `<2*beta`
bound and cast the standard numerical beta>=46 bound into V, preserving the
actual kernel's nonnegative second port. The generic fact argument needs only
these inequalities and positivity; it does **not** use compact44's beta,
fixed-kernel bytes or a Mersenne-specific q-divisibility result. That does not
identify current raw payloads or a physical PDF with the Lean expression.

Finally, all proposed draft imports, tactic elaboration, exact names, model
instances, package objects, source/object ancestry and axiom reports remain
open. Even a successful all-model fact theorem needs the relevant
model-to-internal-proof bridge and coherent endpoint assembly; it alone does
not prove iPRA derivability.

Reproduce the bounded interface scan from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/adaptive87-cfold-cal-model-interface-audit/check.py | cmp - research/adaptive87-cfold-cal-model-interface-audit/receipt.json
```

The scan does not execute Lean or inspect a full provider closure.
