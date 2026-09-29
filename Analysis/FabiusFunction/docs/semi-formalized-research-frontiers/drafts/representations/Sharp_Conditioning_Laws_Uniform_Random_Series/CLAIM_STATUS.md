# Claim and proof status

## Proved in the manuscript

1. **Theorem 2.1:** Sharp variance-fraction TV and relative-entropy profiles,
   endpoint fraction-one separation, and independence of exponential slack
   from every block with a subunit limiting variance fraction.
2. **Theorem 4.3:** A local central limit theorem for every selected tilted
   sum whose variance diverges. This holds for arbitrary positive summable
   weights; the proof uses the classical preserved log-concave shape.
3. **Theorem 5.1 and Corollary 5.2:** Saddle normalization, exponential slack
   with convergence of all fixed nonnegative moments, full-law entropy,
   and the sharp leading overlap asymptotic.
4. **Corollary 7.2:** The sharp independent-exponential prefix threshold for
   geometric/Fabius sums.
5. **Theorem 8.1:** The entire right-hand boundary tail converges in total
   variation along a fixed geometric phase, jointly with independent slack.
   Its law genuinely depends on the phase.
6. **Theorem 9.1:** A Brownian-bridge functional limit jointly with independent
   exponential slack for geometric weights.
7. **Propositions 10.1–10.2:** Explicit variance clocks for stretched-
   exponential and polynomial weights.
8. **Theorem 11.1:** An exact-real lazy rejection sampler, almost-sure
   termination, and its asymptotic expected scalar-uniform draw count.

## Classical tools and background, not originality claims

Exponential tilting; Gibbs conditioning; growing-block conditional limit
questions; convolution preservation of log-concavity; the one-dimensional
Prékopa–Leindler mechanism; Gaussian central limit theory; basic
finite-simplex/beta identities; and accept–reject sampling.

The paper reproduces the analytic arguments needed for its application,
including a log-concave weak-to-uniform density upgrade. Reproving a
classical lemma does not create a claim of priority for that lemma.

## Executed diagnostics, not proof certificates

Five symbolic identities and 72 polynomial integral checks passed. Numerical
quadrature comparisons and 480,000 tilted proposals were run. These validate
formulas and implementation choices, but do not establish the asymptotic
theorems by numerical evidence. The numerical simulation is neither an
exact sampler nor a formal proof checker.

## Explicitly not claimed

- Lean verification or a repository build of the new results.
- External peer review or an exhaustive worldwide priority search.
- Resolution of a specifically named published open conjecture.
- Quantitative uniform error bounds near variance fraction one.
- An exact random-bit implementation or bit-complexity theorem.
- Optimality of the sampler among all possible algorithms.
- A multivariate, nonuniform-coordinate, or random-weight extension.

The main proposed contribution is the moving-tilt infinite-series theorem
package and its configuration-level consequences. Its relationship to the
full earlier conditional-limit literature remains subject to priority review.
