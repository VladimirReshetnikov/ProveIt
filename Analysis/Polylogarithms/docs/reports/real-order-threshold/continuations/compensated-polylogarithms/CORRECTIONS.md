# Audit and correction ledger

## Status changes, not retractions

The inspected prior finite signed-measure theorem is not refuted. Its exact domain remains `a+b >= 1`. The new positive construction below this boundary uses compensated moments and an infinite measure, not a finite signed measure.

The explicit prior conjectures `conj:subcritical` and `conj:constant` now have proofs in Theorems 4.3 and 7.2 of this article. The separate question about subcritical slit-plane nonvanishing is answered by Theorem 4.1. Critical normalized-radius monotonicity was already proved; the new result extends it throughout `a+b <= 1`.

## Corrections required in an unrestricted extrapolation

**Do not split infinite integrals.** For `a+b<1`, both separate terms in `integral 1 dnu - integral u^(n-1) dnu` diverge. Only `integral (1-u^(n-1)) dnu` is legitimate. The finite geometric measure is `domega=(1-u)dnu`.

**Do not claim ordinary boundary convergence.** At total weight below one, the coefficients grow; on total weight one, they tend to a nonzero limit. The new Gaussian/Euler evaluations are analytic or Abel values in these regimes.

**Do not omit the unit-radius existence argument.** A positive endpoint test by invalid dominated convergence is insufficient when `integral domega/(1-u)` is infinite. The proof bounds the negative tail by `2 omega((m,1))` and keeps a positive interior contribution. This is what proves existence at radius one.

**Do not drop the strict-depth normalization.** At depth `d`, the positive order-one Hausdorff sequence is `c_(n+d)/binomial(n+d-1,d-1)`. For depth two with indices `(1,1)`, the unnormalized three terms have second difference `-1/24`. This counterexample rejects an unnormalized assertion; no such false assertion was attributed to the inspected prior report.

**Do not conflate strict and star indices.** The nearby 2026 star-polylogarithm theorem has a different summation convention and normalization. Exact generalized Stieltjes order is not a theorem about arithmetic non-reducibility of a period.

**Keep constant domains explicit.** The older uniform Euler constant one remains valid on its stated domain `a>=1`. The new all-positive bound `H_2^(b)<2` is not asserted optimal. The exact critical constant `pi/4+log(2)/2` is sharp on the critical line. The bound `(1+sqrt(2))/2` on the closed subcritical triangle is valid but not asserted sharp.

## Editorial integration

Use the current manuscript's actual input list, rather than copying a stale chapter path from an earlier package. The inspected main file uses `chapters/05-certified-computation.tex`; the earlier threshold report's suggested `chapters/05-signed-kernels.tex` path should be mapped editorially to the relevant current section.

S4 remains previously proved. S6 and the broad supercritical normalized-radius conjecture remain unresolved by this continuation. The research conjecture about `d-1` angular zeros at arbitrary depth is proved here only at depths one and two, and for sufficiently small radius at each fixed positive index vector.
