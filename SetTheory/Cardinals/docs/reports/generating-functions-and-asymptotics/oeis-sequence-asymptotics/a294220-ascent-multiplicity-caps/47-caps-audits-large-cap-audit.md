# Independent audit of the large-cap expansion

Audited 1 October 2026 against `large-cap-asymptotic.md` and the definition of `T_b` in `general-cap-proof.md`.

**Verdict: the argument is correct. No substantive gap was found.** It proves

    T_b - pi^2/6 ~ (b+1)/2^{b+2},
    6/pi^2 - 1/T_b ~ 9(b+1)/(pi^4 2^b).

All constants implicit below can be chosen independently of b after fixing one c in (2/e,1).

## Checks of the analytic estimates

1. **Reference integral and positivity.** The representation

       f(x) = integral_0^1 (1+t(x-1))^{-1} dt

   extends smoothly to x=1, gives f'<0 and f''>0, and yields
   `integral_0^infinity f(e^v)dv = integral_0^infinity v/(e^v-1)dv = pi^2/6`
   by a nonnegative geometric-series expansion. Hence the stated nonnegative difference integral is exact.

2. **Small interval.** On [0,2], both f'(e^v) and f' between E_b(v) and e^v are bounded absolutely. The remainder bound follows directly from

       sum_{k=b+1}^infinity v^k/k! <= v^{b+1} e^v/(b+1)!.

   Consequently Delta_b, its linear approximation, and the absolute value of its main approximation have integrals O(2^b/(b+1)!) there.

3. **Uniform Poisson estimate.** If N has Poisson mean cb, then
   `Pr(N>=b+1) <= Pr(N>=b) <= exp[-b(c-1-log c)]`,
   using the Chernoff parameter log(1/c). Poisson-tail monotonicity extends this bound to every v<=cb. The exponent is strictly positive for 0<c<1.

4. **Uniform Taylor remainder.** For x/2<=xi<=x, set A=1+t(x-1). The inequalities

       1+t(xi-1) >= A/2,      t/A <= 1/x

   give `f''(xi) <= 16[-f'(x)]/x`. With R=e^v-E_b(v), Taylor's theorem therefore gives the explicit bound

       0 <= Delta_b(v)-L_b(v) <= 8(R/e^v)L_b(v).

   This verifies the claimed relative error uniformly on [2,cb]. The derivative expansion is uniform for v>=2, and its integrated error is bounded by

       integral_0^infinity v e^{-3v} R_b(v)dv
         = sum_{k=b+1}^infinity (k+1)/3^{k+2}
         = O(b 3^{-b}),

   with Tonelli's theorem applicable because all terms are nonnegative.

5. **Large-v tail.** Stirling gives `(cb)^b/b! -> infinity`, so E_b(v)>=2 throughout v>=cb for large b. Using log E_b(v)<=v gives exactly

       integral_{cb}^infinity Delta_b(v)dv
         <= 2b!(cb)^{2-b}/(b-2)
         = O(b^{3/2}(ec)^{-b}) = o(b2^{-b}).

   Convexity gives L_b<=Delta_b. On v>=2, the main approximation `(v-1)e^{-2v}R_b(v)` is nonnegative and at most L_b(v). Thus the same tail estimate legitimately controls both omitted integrals.

## Termwise integration and final constant

For explicit absolute-integrability justification of the signed leading integrand, use

    sum_{k=b+1}^infinity integral_0^infinity
      |v-1| e^{-2v} v^k/k! dv
    <= sum_{k=b+1}^infinity [(k+1)/2^{k+2} + 1/2^{k+1}] < infinity.

Fubini is therefore valid, including the negative part on (0,1), and gives

    M_b = sum_{k=b+1}^infinity (k-1)/2^{k+2}
        = (b+1)/2^{b+2}.

The three additive errors, divided by M_b, tend to zero: their orders are respectively `(2/3)^b`, `b^{1/2}(2/(ec))^b`, and `4^b/((b+1)!(b+1))`. The relative Taylor error also tends to zero. This establishes the first equivalence without assuming T_b's limit in advance. It implies T_b->pi^2/6, and the reciprocal identity then gives the second equivalence with coefficient 9/pi^4.

The numerical table is not needed for this audit or the proof. The absolute-integrability bound above is a useful optional clarification of the original argument, not a missing hypothesis or a correction.
