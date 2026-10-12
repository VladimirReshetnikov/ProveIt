# Proposed integration

Suggested new report directory:

`Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/continuations/balanced-stieltjes-moments/`

This is a proposed path, not an assertion that the remote path is empty.
No remote commit, branch, pull request, or repository write was made.

## Files to retain

Retain the standalone `article/` TEX and PDF, `code/`, the verification JSON
files, README, requirements, and build script. The supplied source compiles
independently; it should not be inserted wholesale into another document
with a second preamble. The concise `manuscript_fragment.tex` supplies an
optional entry point and uses the `bsm:` label namespace. The standalone
article's labels are namespaced as well.

## Dependency and proof status

1. Establish the local uniform shifted Hurwitz expansion and its coefficient
   cancellation.
2. Prove the Mellin transform by the explicit one-tail cutoff argument.
3. Use the finite Gamma quotient to remove integer poles, distinguishing a
   zero of Q from a zero of the Bernoulli polynomial.
4. Add the finite-filter criterion and the jointly holomorphic mixed germ.
5. Add the argument-derivative and anchored-primitive consequences.

Analytic proofs are supplied in the article. Exact finite replay and
high-precision numerical diagnostics are separate forms of evidence; neither
is claimed to be a Lean or other proof-assistant formalization. Do not promote
S6, revised S8, or the distinct R_{r,k} coefficients on account of this report.

## Normalization checklist

- Conventional Laurent sign: zeta(1+z,a)=1/z+sum (-1)^n gamma_n(a)z^n/n!.
- C_q is a derivative, not a Taylor coefficient: C_q=partial_z^q F(0).
- Q_q=q! [z^q] Gamma(u+z)/(Gamma(u)Gamma(1+z)).
- B_1(a)=a-1/2.
- At q>=m, moments use the finite kappa_{m,q} Bernoulli formula.
- At q=m-1 and B_m(a)=0, use a Hurwitz order derivative instead.
- Combine all shifted terms before integrating. Never separately integrate
  nonconvergent summands.
- Elementary harmonic coefficients govern balanced moments; complete
  homogeneous ones govern raw order moments on the vertical mixed-germ axis.
- Preserve order derivatives [r] versus argument derivatives (r).

## Read before accepting novelty or editing predecessors

`SOURCE_AUDIT.md` records the bounded source scope, unexpanded incoming
archives, and an independently confirmed duplicated README paragraph. Review
current versions before changing anything. No mathematical error in a cited
predecessor is asserted merely because a tempting extension would be invalid.

## Reproduction and diagnostics

Run all four verification scripts, then `python build.py`. The main numerical
suite uses 55 working digits, and the special-value suite uses a step-refined,
12th-order centered order derivative for polylogarithms. The earlier failed
near-integer automatic-differentiation diagnostic is retained explicitly as
an exploratory failure, not included in the passing suite totals.
