# New-source review and the logarithmic-order question

Research notes for integration in the current report. These notes contain a conditional transfer proposition and a proved, explicitly restricted obstruction. They do **not** establish a smaller worst-case SAT exponent order.

## 1. Exact source and statement scope

The user-supplied revision is `anthropics/formal-math@1a6eee293b9e00cb432eef6018a21f523623a9af`, committed 2026-10-26 at 19:45:07 PDT. Its `eth/` directory supplies the paper and proof sources. The checked-out tree contains 1,052 `.lean` files, of which two are checking scripts; the paper describes 1,050 modules in the development. Do not carry forward the earlier repository summary's assertion that this proof is unpublished.

Inspected primary files:

- https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/eth/README.md
- https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/eth/MainResults.lean
- https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/eth/Solution.lean
- https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/eth/comparator.json
- https://github.com/anthropics/formal-math/blob/1a6eee293b9e00cb432eef6018a21f523623a9af/eth/paper.pdf
- `eth/proof/README.md`, `eth/proof/PaperIndex.lean`, and `eth/scripts/PrintAxioms.lean` at the same revision.

`MainResults.lean` imports only Mathlib and contains definitions, including the two target propositions. `MainResults.MainTheorem` quantifies one finite-alphabet Mathlib multi-stack Turing machine and one constant C **before** the width k and the formula. Its time is

    2^{C min{ k m / sqrt(log_2 m),
                k^2 n log_2(log_2 n) / sqrt(log_2 n) }}.

The conditions are k >= 1, n >= 4, m >= 2, no repeated clause-list, clauses of width at most k, and every declared variable occurs. The output is the exact count in n+1 bits. This is a uniform-in-k statement, not merely an algorithm separately selected for each fixed k. `ETHIsFalse` is the negation of positivity of the infimum of achievable deterministic 3-SAT exponential rates.

`Solution.lean` supplies unconditional proof terms from `CountedRoute.mainTheoremHolds`; the ETH consequence passes through `NamesInOrder` and `Wrap`. It imports no `Challenge` module. A textual scan found only two actual `sorry` terms, both intentionally in `Challenge.lean`, the reference statement used by Comparator. The supplied comparator configuration permits only `propext`, `Quot.sound`, and `Classical.choice`, and enables nanoda. The proof README explains the intermediate operation-count and padding model and why the final theorem is nevertheless stated in concrete Turing-machine steps.

**Verification scope:** these are source-inspection findings. We did not build the development, run Lean's kernel, replay leanchecker, run Comparator/nanoda, or independently audit all transitive proofs. The README and Appendix E report those upstream checks; attribute them to the source if mentioned. The theorem contains no memory bound, so this material must not be described as a polynomial-space theorem without an additional proof.

The new PDF and the previously filed ProveIt PDF are both 49 pages but not byte-identical:

| File | Bytes | SHA-256 |
|---|---:|---|
| New `eth/paper.pdf` | 900337 | `7af518b09342c967ea371c74b8989806684c5d02aabe5763ca08554aff5025a0` |
| ProveIt `Research/claude-2o-n-3sat/eth.pdf` | 868673 | `f0af035b6c87d04d3fcf07dae040df98029f4990c6493e3e9ab64c4ac714c0eb` |

Text comparison shows additions to provenance, citations, and formalization/publication status, with layout changes. The inspected main theorem and Appendix B rate remain the same. This is not a claim of complete semantic identity of every paragraph.

## 2. What is algorithmically different

The new source contracts complete graphs with arbitrary integer-valued node tensors. It expresses the crossing tensor `[x=v][y=u]` as a sum of pieces, each admitting two factorizations: by rows `(x,y)|(u,v)` and by columns `(x,u)|(y,v)`. The algorithm chooses the cheaper whole-grid grouping and then balances the resulting network.

For a lambda-bit crossing, Definition 7 asks for polynomially many pieces, computable in `2^{O(lambda)}` operations with controlled integer sizes, whose factorization bit costs satisfy

    c_row + c_col <= 4 rho lambda + O(log lambda).

Theorem A converts such pieces into a rate

    e(K) = O((log K)^(-alpha)),  alpha = log_2(1/rho),

and then a fixed-width SAT exponent `O(n log log n / (log n)^alpha)`. The improved schedule has `log K_l = Theta(2^l)`, while `e_l = Theta(rho^l)`.

The simple eight-square decomposition has rho=11/12. Appendix B instead uses graded polynomial operators, their exact locality identity, and the partition dimensions `dim V_E = p(E)`. Because `log_2 p(E) = c sqrt(E) + O(log E)`, the factorization ranks give rho=1/sqrt(2), hence alpha=1/2. This is a different mechanism from the OpenAI Cauchy/2-adic deformation, even though both final rates have the same square-root logarithm.

The one-line singlet hint in the README only targets failure of ETH for every fixed delta; its displayed recurrence is not a substitute for the sharper Appendix A/B proof.

## 3. Why the most direct composition does not improve the order

The earlier ProveIt precision packet gives an exact rank encoding of the mode sum. For a first-stage group count r, the collision-packing budget permits, at the level of the existing certificate,

    u = O(log M / log r).

The resulting mode-index graph has entropy/bit budget on the scale

    B = O(M / sqrt(u))
      = O(M sqrt(log r) / sqrt(log M)).

The OpenAI contraction theorem cannot simply be invoked on this graph: at constant or polylogarithmic r, some group tensors have degree comparable to B/r. The new Anthropic clique result does allow arbitrary tensor entries, and so supplies a more appropriate *possible* backend after paying its balancing, entry-query, and representation costs.

However, its rate in the number of groups is `e(r) = O(1/sqrt(log r))`. At the scale of these two certificates their product is

    B / sqrt(log r) = O(M / sqrt(log M)).

Thus the apparent extra square-root factor is spent obtaining the first-stage grouping. A smaller r leaves the backend improvement a constant; a growing r reduces the first retained-level range. This algebra is a diagnosis of the proposed composition, **not** a lower bound on an implementation or on tensor contraction. It is also not a complete composition theorem: balancing and expensive group-entry evaluation still must be charged, and can only make this particular certificate less favorable. The new source repairs an important type mismatch but does not, on its own, close the previously missing `M/log M` summation interface.

## 4. Conditional graded-dimension transfer

Appendix H, page 49, already observes that replacing the square-root growth of `log dim V_E` by growth like `E^beta` would give `rho=2^{beta-1}`. The proposition below makes that source suggestion into an explicit algorithmic interface, including matching upper/lower leading constants and evaluation costs. The growth-to-rate idea belongs to the source; no new conceptual route is claimed for restating it. No construction satisfying it with beta<1/2 is supplied here. Section 5 adds a restricted obstruction to its most immediate sparse-oscillator implementation.

Assume that for some fixed `0 < beta < 1`, an integer/rational graded operator system supplies the exact identities and dual families required in Appendix B, and let `d_E = dim V_E`. Require:

1. `d_E` is nondecreasing, with
   `log_2 d_E = A E^beta + O(log(E+2))` for a fixed A>0.
2. For the least h such that `d_h >= 2^lambda`, the crossing has an exact sum of `poly(h)` pieces. Each piece indexed by s has row and column ranks bounded, respectively, by `poly(h) d_{2h+s}` and `poly(h) d_{2h-s}`, for `|s| <= 2h` (zero negative-degree spaces may be used).
3. The integer multiplier, pieces, factorization maps, bases, ranking, and evaluation are all constructible with the quantitative bit-size and `2^{O(lambda)}` work guarantees of Definition 7. A dimension estimate alone does not imply this condition.

**Conditional proposition.** These hypotheses give pieces with

    rho = 2^{beta-1},  alpha = 1-beta.

**Proof.** Minimality of h and the two-sided growth estimate imply

    A h^beta <= lambda + O(log(lambda+2)),
    h = Theta(lambda^{1/beta}).

For fixed s, taking logarithms of the two rank bounds gives

    c_row + c_col
      <= A [(2h+s)^beta + (2h-s)^beta] + O(log h)
      <= 2 A (2h)^beta + O(log h)
      <= 2^{beta+1} lambda + O(log(lambda+2)).

The middle inequality is concavity of x^beta. This is Definition 7 with `4 rho = 2^{beta+1}`. All remaining algorithmic requirements are explicit hypotheses. Theorem A then has `alpha=log_2(1/rho)=1-beta`.

In particular, beta=1/3 would give, for fixed k, the conditional bounds

    arbitrary density: poly(n,m) 2^{O(n log log n / (log n)^{2/3})};
    fixed density:     poly(n,m) 2^{O(n / (log n)^{2/3})}.

No operator system meeting these hypotheses with beta<1/2 has been constructed here. The condition must retain the *same leading growth coefficient A* in the upper and lower dimension estimates; merely knowing `log d_E=Theta(E^beta)` does not identify the claimed rho.

## 5. A proved obstruction for independent sparse oscillators

A tempting proposal keeps only variables with square weights,

    Q[t_1, t_4, t_9, ...],  weight(t_{j^2})=j^2,

hoping to use the smaller square-part partition growth in the preceding transfer. This fails at the exact locality step: the current's commutator series has the form

    C(z) = sum_{j>=1} j^2 z^{j^2}

(up to an irrelevant monomial shift or nonzero normalizing coefficients). No polynomial can clear this series to a polynomial.

**Lemma 1 (gap obstruction).** Let `C(z)=sum_{n>=0} c_n z^n` over a field. If C is rational and not a polynomial, its nonzero coefficient support has bounded gaps after a finite prefix.

**Proof.** Write `Q(z) C(z)=P(z)` with `Q(0) != 0` and `d=deg Q`. Above deg P the coefficients obey

    q_0 c_n + q_1 c_{n-1} + ... + q_d c_{n-d} = 0.

A string of d consecutive zero coefficients in this tail forces all subsequent coefficients to be zero by induction. That would make C a polynomial, a contradiction. The case d=0 already gives a polynomial. Hence such arbitrarily long zero strings are impossible.

The square series has nonzero terms at every positive square and arbitrarily long zero strings between squares. It is not rational. In particular it cannot satisfy the polynomial-clearing locality used in Appendix B: multiplying by a fixed power of `(omega_1-omega_2)` would imply rationality of its one-variable positive expansion.

There is a stronger restricted conclusion.

**Lemma 2 (growth obstruction for independent oscillators).** Let S be an infinite subset of the positive integers and suppose a rational, nonpolynomial commutator series has nonzero coefficient support S. Consider the free polynomial Fock space with one independent variable of weight n for each n in S. Its cumulative graded dimension obeys

    sum_{j<=E} dim V_j >= 2^{c sqrt(E)}

for a constant c>0 and all sufficiently large E.

**Proof.** By Lemma 1, some fixed d bounds the gaps in S after a finite prefix. Thus for sufficiently large B, there are at least `B/(2d)` members of S at most B. Choose independently exponent 0 or 1 on those generators. This gives at least `2^{B/(2d)}` distinct monomials. Each has weight at most `B * |S cap [1,B]| <= B^2`. Set `B=floor(sqrt(E))`.

Consequently a free independent-oscillator construction with exact rational locality cannot have uniform graded growth `log dim V_E = O(E^beta)` for beta<1/2: summing that upper bound up to E contradicts Lemma 2. Restricting to a finite set of oscillators is not a workaround for the original two-sided current: its nonzero commutator becomes a finite Laurent polynomial, which cannot be annihilated by a nonzero polynomial in a domain. Both arguments concern this specified current/independent-generator model. They are **not** obstructions to all graded algebras, vertex-algebra quotients, nonlocal deformations, signed tensor algorithms, or SAT.

The independence premise is automatic in any characteristic-zero vacuum representation that retains the nondegenerate Heisenberg relations. More explicitly, suppose a nonzero vacuum v is annihilated by all positive operators `a_n`, the operators `a_{-n}` raise weight by n, positive operators commute, negative operators commute, and

    [a_n, a_{-m}] = delta_{nm} c_n Id,   c_n != 0 for n in S.

For any finite exponent tuple alpha of weight E, applying the annihilator monomial `prod a_n^{alpha_n}` to a linear relation among creation monomials of the same weight E kills every monomial except `prod a_{-n}^{alpha_n} v`. Indeed, any different tuple beta of the same weight has some beta_n < alpha_n. The surviving coefficient is multiplied by the nonzero scalar `prod alpha_n! c_n^{alpha_n}`. Hence all creation monomials are linearly independent. Thus a quotient preserving these vacuum and Heisenberg premises cannot remove the growth obstruction either. A quotient with different, noncentral commutators is outside this result.

This converts the square-weight idea from an unsupported improvement into a sharply defined negative result: a successful smaller-growth construction must change the operator relations or exact recovery identity, rather than merely delete oscillator modes or quotient while preserving the above Heisenberg premises.

## 6. Research questions with concrete proof obligations

1. Find a nondegenerate graded operator system with beta<1/2 satisfying all three transfer hypotheses. Relations that lower the Hilbert growth must preserve dual pairing and the exact crossing identity while escaping the Heisenberg premises above; simply thinning a free oscillator spectrum or quotienting it without changing those premises fails.
2. Replace polynomial locality by an exact alternative recovery mechanism with quantitative rank and bit-cost control. Approximate or truncated commutators are insufficient unless their residual error is proved to vanish in the counting ring.
3. Analyze cross-source mode compression plus clique contraction with complete accounting. A useful outcome could be a better coefficient or memory tradeoff, but a claimed order gain must overcome the displayed budget cancellation and entry-query cost.
4. Exploit relations among actual group tensors to bypass explicit mode tables. The current full-table lower envelopes constrain a representation, not the algebraic values in it.

