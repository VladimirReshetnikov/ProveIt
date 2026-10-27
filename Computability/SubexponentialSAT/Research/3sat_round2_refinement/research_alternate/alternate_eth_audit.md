# Alternate 49-page ETH manuscript: source-only audit

Audit date: 2026-10-27 UTC. No supplied source program, proof build, installer, or benchmark was executed. Read-only PDF inspection used `pdfinfo`, `pdftotext`, and selected-page rendering. This is a mathematical/source assessment, not a certification of the paper or its claimed formal proof.

## 1. Identity and provenance boundary

- Local source: `../sources/proveit/eth.pdf` (49 pages; 868,673 bytes).
- SHA-256: `f0af035b6c87d04d3fcf07dae040df98029f4990c6493e3e9ab64c4ac714c0eb`.
- Supplied immutable repository pin: `aa6933442eb936962de79ba6d321cd0391c450bd`.
- Printed title: *A 2^{o(n)} Time Algorithm for 3-SAT*.
- Printed attribution: **CLAUDE / ANTHROPIC**. This is attribution in the supplied document, not independent authentication of organizational authorship.
- Printed date, p. 1: October 26, 2026, 3:13 PM PT. PDF metadata dates are fixed at 1979-12-31 and do not establish creation time.
- This is not `paper.pdf`: that separate 67-page document is attributed to OpenAI, titled *The Exponential Time Hypothesis is False*, dated October 17 / revised October 25, 2026; SHA-256 `5b1612dc2eebb2cad5b4cbe62d1fed2982f01ab1908c26f70010a651487e8123`.
- The acquisition agent reports the import commit calls `eth.pdf` a separate manuscript, with no Lean files added alongside it. Its completed immutable path inventory covers 223,088 descendants, with 29 subtree queries, zero errors, and all four truncated trees split recursively. It found no separately named ETH/3SAT/SubexponentialSAT proof/source subtree outside incoming; the four submodules concern other projects. This is not a proof of absence under arbitrary hidden names, but the claimed proof development was not found. Evidence is in `../sources/proveit/path_inventory_summary.json`, `tree_queries.json`, `eth_path_matches.json`, and `path_inventory.tsv`. This audit does not substitute the PDF's claims for a proof inventory.

## 2. Actual strongest printed theorem and comparison

Theorem 1, pp. 1-2, equation (1), claims one deterministic exact #k-SAT algorithm with

`2^{O(min{k^2 n log log n / sqrt(log n), k m / sqrt(log m)})}`

time, where the hidden constant is absolute. Logs are base 2. Its input is a set of clauses, each with at most k literals; n counts variables that actually occur. Corollary 11, p. 34, equation (58), makes the ranges `k >= 1`, `m >= 2`, `n >= 4` and a common absolute constant explicit. It combines the m- and n-algorithms by alternating their steps. For N declared variables, n of which occur, multiply by `2^{N-n}` after polynomial-time normalization.

For fixed k=3:

- Arbitrary density: `2^{O(n log log n / sqrt(log n))}`.
- Fixed density `m=O(n)`: `2^{O(n / sqrt(log n))}`.
- These are the **same worst-case exponent orders** as the strongest OpenAI Theorem 1.1 / Appendix D bounds, not an improvement on them.
- The alternate theorem has an explicit uniform dependence `k^2` in the n-exponent and absolute hidden constant; the OpenAI stated result fixes k and explicitly includes polynomial space. These are different scopes/guarantees, not an established asymptotic speedup for fixed-width 3-SAT.
- This alternate paper does not state a matching polynomial-space theorem. Do not silently attribute the OpenAI space guarantee to it.
- Theorem 2, p. 4, is deliberately weaker: for each delta > 0 a possibly delta-dependent deterministic algorithm runs in O(2^{delta n}). The strongest theorem is in the appendices, not only the main-body recursion.

## 3. Distinct algorithmic architecture

This is a genuinely different presentation/route from the OpenAI Cauchy deformation, two-adic precision, and tensor-mode recursion, despite the matching final orders.

1. A clause network shares variable-consistency bits along occurrence chains; its total is O(km), not quadratic in occurrences (pp. 5-6, 19-20).
2. Networks have arbitrary signed integer local tables and explicit integer factorizations across edges (Definitions 1-4, pp. 14-15). Tables are query-access, not necessarily written out.
3. Put clique nodes on a grid, replace each pair of crossing equalities with a signed sum of pieces, and for each resulting global term choose all rows or all columns. The choice is **global per term**, not independent per rectangle (Proposition 3, pp. 17-18, equation (36)).
4. Balance the resulting network and recurse. The main body uses the eight-square identity with contraction rho=11/12 and only fixed-parameter polynomial factors.
5. Appendix A explicitly redoes costs when the number of nodes grows with the input. Definition 7, pp. 26-27, is the exact reusable contract for a family of pieces: polynomially many indices in lambda, an integer multiple of the crossing, combined row/column factorization cost at most `4 rho lambda + c log(2 lambda)`, effective evaluation in `2^{c lambda}`, and polynomial bit lengths.
6. Theorem A, pp. 27-29: if the pieces have parameter rho, the denominator exponent is `alpha' = log_2(1/rho)`; `K_{ell+1}=g_ell^2` with `g_ell=2^{3 ell+x0}K_ell`, and `e_ell=Theta(rho^ell)=Theta((log K_ell)^{-alpha'})`.
7. Appendix B, pp. 29-33, replaces the octonion pieces with polynomial-ring operators / integer partitions. Theorem B gives rho=`1/sqrt(2)`, hence alpha'=1/2. Formula (56), p. 32, is the central cost inequality.
8. Appendix D, pp. 34-39, removes the poor sparsification dependence in the n-bound by truncated inclusion-exclusion plus sparse parity checks, modular truncation, and variable-node networks. The network total becomes `U=O(kn log Delta)+2g^2` in equation (68), rather than O(km). Sparsification yields `log Delta=O(k log(k/e))`, giving `O(k^2 e n log(k/e))` in the exponent. For e=Theta(1/sqrt(log n)), this is the claimed n-bound.

## 4. Proof-status assessment and exact outstanding checks

### Printed proof

The inspected chain is substantive and does not merely assert the end result. In particular, it supplies explicit finite piece indices and integer factorizations, uniform cost accounting for growing K, a deterministic exhaustive-search replacement for the probabilistic existence arguments, and modular recovery conditions for exact counting. No specific internal contradiction was identified in this bounded audit. That is **not** a proof certificate or a claim that every argument has been independently verified.

Outstanding proof-audit obligations:

- Appendix B Lemma 9, pp. 30-31: the formal Laurent-series/locality calculation is the central algebraic step. The paper proves it rather than only citing vertex-algebra theory, but this audit has not independently reconstructed every coefficient identity.
- Appendix C, p. 33, is explicitly labeled a **proof sketch**. Its disjointness trick carries forced negative unit clauses in a separate list N that does not affect the original sparsification branch choices. The partition-of-assignments argument is explicit; the quantitative recursion bounds are imported from Calabro.
- Appendix D Step 5, pp. 38-39, relies on precise external sparsification thresholds and bounds from Calabro [Cal09], notably Figure 5.1, Lemmas 5.3/5.13, and equation (5.4). Those cited external documents were not independently audited here. The paper itself says the formal development uses its own analysis with thresholds assumed to be Calabro's, not checked against the dissertation (p. 44).
- Model conversion and encoding are explained but not part of the claimed Lean statements/proofs (pp. 41, 43). They are standard-looking polynomial-overhead arguments, not an obvious fatal gap; their exact model correspondence still needs independent checking.
- Absolute constants remain nonexplicit. The paper notes that without an explicit piece constant c its construction asserts existence, not a fully instantiated optimized solver (p. 29).

### Claimed formalization versus available evidence

Appendix E, pp. 40-44, says:

- BOTH `MainTheorem` (the strongest bound, not only the weaker subexponential corollary) and `ETHIsFalse` have been proved in Lean 4.33.1 over Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.
- The development allegedly has 1,881 Lean files, was rebuilt, uses only the standard `propext`, `Classical.choice`, `Quot.sound` axioms, and was checked by Lean's kernel, `leanchecker`, and through Comparator by `nanoda`.
- The printed listing is explicitly **definitions only; no theorem and no proof**. The actual proof is said to be in a separate file.
- The full proof link is literally a placeholder: `[Link to the full Lean proof: to be added when a public location exists.]`
- At time of writing, no person is known to have checked the development. Models compared the printed and Lean routes, and the strictest considered the latter a different proof of the same statement.
- Formal running time uses deterministic finite-alphabet multi-stack machines. The intermediate oracle machine permits polynomial-time state operations and padded computations, losing constant powers absorbed by the final exponent's O-constant. In particular the pieces algorithm pads by about `2^{c lambda}` ones before a single polynomial-state-time step (p. 44).

Therefore: this PDF supports a **claim of a strongest-bound formalization**, but it does not supply auditable proof bodies or independently verify the advertised builds/checks. It must not be described either as a verified full formal proof or as merely the weaker Lean theorem from the other packets.

## 5. Promising structural lever, with rigorous obstruction

Appendix H, pp. 48-49, identifies the important general mechanism. Two operator orders pass through graded pieces of sizes controlled by `dim V_{2h+s}` and `dim V_{2h-s}`. If `log dim V_E ~ C E^alpha`, and the same crossing identity, dual basis, locality and effective-piece conditions all hold, concavity would give

`rho = 2^{alpha-1}` and `alpha' = log_2(1/rho) = 1-alpha`.

An effective replacement with alpha<1/2 would therefore improve the actual asymptotic denominator power beyond sqrt(log n), not just a constant. **The document does not construct such a replacement.** Its existing space has `dim V_E=p(E)` and alpha=1/2.

### Why merely thinning or regrading the existing Heisenberg construction is not enough

The following is a new elementary deduction from the exact algebra in the source, not a result claimed by the paper.

Let W be a characteristic-zero graded vector space with nonzero vacuum v in degree zero. Suppose there are positive-energy creation operators a_{-m}, annihilators a_m, for every positive integer m, satisfying:

1. a_{-m} has degree m and a_m degree -m;
2. like-sign operators commute;
3. `[a_m,a_{-n}]=m delta_{mn} Id`;
4. `a_m v=0` for every m>0.

For every partition multiplicity vector beta with sum m beta_m=E define

`v_beta = product_m a_{-m}^{beta_m} v`.

These p(E) vectors are independent. To isolate beta in a same-energy linear relation, apply `product_m a_m^{beta_m}`. For another multiplicity vector gamma of the same weighted sum, gamma!=beta implies beta_m>gamma_m for some m. Commuting annihilators to the right then kills that term. The beta term equals

`(product_m m^{beta_m} beta_m!) v`,

which is nonzero in characteristic zero. Hence `dim W_E >= p(E)` and `log dim W_E >= Theta(sqrt(E))`. A nonzero quotient preserving these exact relations cannot have alpha<1/2.

Source anchors: Appendix B p. 30 defines `V=Q[t_1,t_2,...]`, weighted piece V_E, `nabla_{-m}=t_m`, and `nabla_m=m partial/partial t_m`; Appendix H p. 48 equation (76) gives the commutators; p. 49 names the Fock representation.

Two more narrow obstructions clarify the required change:

- A nonlinear regrading such as deg(t_m)=m^q may lower the entropy but destroys the exact homogeneous shift (O1) used in Appendix B: definition (47) groups products by sum k_i=-r, and with nonlinear mode degrees those summands no longer all have degree r. Linear rescaling preserves alpha=1/2.
- Keeping only an infinite sparse set S of modes breaks ordinary finite-order locality of the current. Its commutator coefficients are `c_j=j*1_{|j| in S}`. Multiplication by a fixed power `(z-w)^H` gives a fixed finite difference of these coefficients; locality forces `Delta^H c_j=0`, hence polynomial dependence on j. If S and its positive complement are both infinite, infinitely many zero coefficients force that polynomial to vanish, contradicting retained modes. This only rules out the naive restricted current, not every conceivable new algebra or filtered/approximate construction.

Thus the genuine research target is a **different effective crossing decomposition** (or a different algebra/encoding which preserves enough identities), not a free entropy gain from deleting the present modes. A successful candidate must prove all of Definition 7, especially integer dual factorizations and exact reconstruction of the full crossing. Dimension counts alone do not prove an algorithm.

## 6. Practicality and next audit gate

The manuscript expressly disclaims practical speedups: pp. 2, 29, 39 give astronomical necessary sizes for the proved bounds to beat exhaustive search. Its own end-of-Appendix-D estimate is `n > 10^{10^8}`; the fixed density example m=5n is beyond `10^{10000}` as summarized on p. 2. These are bound-level thresholds, not measured runtimes.

The next useful evidence gate is obtaining the actual claimed proof sources plus pinned build/checker artifacts and checking that the theorem types instantiate `MainResults.MainTheorem` rather than a weaker surrogate. Without that, continue mathematical source audit rather than describing the formal claims as established.

Files retained for local verification: `eth.layout.txt`, `openai_appendixD.layout.txt`, and rendered `p32.png`, `p49.png`. Full standalone proofs of the restricted entropy obstructions are in `heisenberg_entropy_barrier.md`.
