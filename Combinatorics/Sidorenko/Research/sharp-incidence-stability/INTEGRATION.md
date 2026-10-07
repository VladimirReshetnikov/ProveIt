# ProveIt integration notes

## Suggested location

`Combinatorics/Ramsey/Research/SharpIncidenceStability/`

This is a proposed new location. No repository changes have been made.

## Initial status

Integrate as a research article with full written proofs and supplementary exact
checks. Do not mark it as Lean-verified or axiom-audited. Do not overwrite the
source Sidorenko manuscript or its comparator with this package.

## Statements to expose

1. **Unit contraction**: normalized integral monotone submodularity is preserved
   by `f'(S) = min(f(S), f(S union {e0}) - 1)` when `f({e0}) >= 1`.
2. **Sharp fractional-cover inequality**: use an explicitly finite maximum and
   positive denominator hypotheses. Separate monotone covers from arbitrary
   submodular fractional partitions.
3. **Uniform incidence-span inequality**: expose `R`, `Delta`, and `mu_a` as
   separate definitions; prove exact one-dimensional quotient identities.
4. **Directness repair and strict-balance equality**: the repair theorem controls
   deletion to a direct sum, not closeness to a common-core extremizer.
5. **Gram constraint count**: keep the ambient span arbitrary; require isotropy
   only of local vertex spans.
6. **Dependent-family count**: distinguish relation-space selection, exterior
   constraint loss, local-rank savings, and Lagrangian containment probabilities.
7. **Source application**: expose the pointwise residual weight bound as an input
   and retain all upstream dimension thresholds.

## Exact replacement boundary in the source

Source folder:

`preprints/A-counterexample-to-Sidorenkos-conjecture-September-23-2026/build/`

At the pinned source commit, the relevant labels in `sections/tail.tex` are:

- `lem:tail-span`: replace or strengthen with the `m_2(G)` inequality;
- `lem:tail-residual-counts`: replace its nondirect estimate using the new
  exterior-algebra argument;
- `prop:singular-tail`: the *additional residual restriction* `D > 1641` may be
  replaced by even `D >= 310`, provided the earlier residue threshold is still
  satisfied. The later transverse threshold remains unchanged as well.

The improvement is not a proof of the full Sidorenko construction at D = 310.
The direct residual exponent agrees with the existing source proof. No claim is
made of an improved global q-rate, a smaller incidence graph, a new numerical
Ramsey bound, or an explicitly optimized finite host order.

## Formalization order

Start with integral/rational finite submodularity, then linear algebra, then
finite graph density certificates. Develop the finite symplectic and exterior
count separately. Real-valued submodularity, entropy, and determinant corollaries
can be added without blocking the graph-count application.

The included Python code is useful for test data and arithmetic certificate
generation, but it should not be imported as a trusted proof oracle.
