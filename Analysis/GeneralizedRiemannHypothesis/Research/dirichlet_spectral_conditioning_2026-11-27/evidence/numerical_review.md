# Independent numerical-method review

A separate model-assisted review examined the simulation code and recorded
JSON without rerunning or changing the sampling algorithms. This is a code
and mathematical review, not an independent random experiment or formal
certificate.

## Conditional rejection sampler

For the explicitly finite model with ordinates j, 1 <= j <= 4096,
the proposal has independent exponential coordinates with rates j^2+t.
The saddle is x=sum_j 1/(j^2+t). Multiplying its density by
`1_{S<=x} exp(t(S-x))` gives a constant multiple of the original joint
density restricted to `S<=x`. The accepted law is therefore exactly that
finite conditional law in ideal arithmetic. The implementation uses
ordinary floating-point arithmetic and pseudorandom samples.

## Product total-variation estimator

For the unit-rate product R and tilted product P with rates 1+epsilon_j,
the code evaluates the exact log likelihood `log(dP/dR)` under each law.
The difference of probabilities of its positive event equals TV(P,R).
The shared exponential proposals are a valid common-random-number
coupling. The paired sample standard error is appropriate for the
differences. It is not an estimate of TV between the conditional law and
the unit-rate product; that comparison is supplied by the analytic theorem.

The output labels `unit_rate_event_probability` and
`tilted_event_probability` identify the two event probabilities explicitly.

## Verified interpretation limits

The conditional finite-model experiment at u=128 has bridge/slack
correlations about -0.083, -0.221, -0.443 at cutoffs 0.5, 1, 2.
The c=2 variance is 0.04863, while its infinite-limit target is 0.03888.
These finite effects are not bugs and should not be described as a
numerical verification of independence.

For the synthetic product experiment at (u,c)=(10000,3), the TV estimate
is 0.72354 with paired standard error 0.00200, compared with the
finite-tau Gaussian profile 0.73762 and the limiting c-profile 0.78642.
The differences are genuine finite-parameter effects, not Monte Carlo
agreement within the reported uncertainty.

No material error was found in the rejection rule, likelihood estimator,
synthetic counting inversion, plotted constants, or recorded model labels.
These checks do not establish theorem novelty or replace the written
proofs of the infinite-spectrum limits.

