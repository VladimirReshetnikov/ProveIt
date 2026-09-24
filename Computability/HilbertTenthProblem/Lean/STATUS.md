# Formalization status

Legend: **proved** (no `sorry`, no project axiom), **Mathlib** (reused from
Mathlib), **pending** (not yet validated), **—** (not started).

Policy (project-owner update, 2026-09-14): **do not introduce new axioms**.
The previous pre-1980 and elementary-fact allowances are superseded.
Verified results may be reused from Mathlib or other Lean developments,
with their dependencies audited. Completed proofs are retained. No
project mathematical axiom or `sorry` is used in the published library.
Earlier dated receipts below describe the policy then in force and do
not authorize new axioms.

Current phase (project-owner update, 2026-09-14): after publishing the
MRDP equivalence milestone, **pause further formalization of the six
papers** and review the existing Lean code. Prioritize shorter proofs,
shared lemmas and helper functions, deduplication, and clearer comments.
Generalize results and prove stronger reusable forms where possible, while
retaining existing interfaces when useful for callers.
The remaining statements below stay open; they have not been removed
from the longer-term formalization scope.

## Progress estimate — 2026-09-14

The current planning estimate is **70–80% of the mathematical development
across the six articles**, or roughly three quarters. This is an assessment
of the arguments and principal statements, not a fraction of source lines,
modules, or numbered claims. Shared results, especially the overlap between
the 1980 announcement and the 1982 article, are not independent work.
Pending proofs in the tables below do not count as completed.

| Article | Approximate mathematical coverage | Main remaining work |
|---|---:|---|
| 1974 | 90–95% | The computability claims about `H` and `Σ` (dovetailing, immunity, degrees, accelerated growth) and the upper halves of the numerical table |
| 1976 | 85–90% | §4 Theorem 4.2 and Corollary 4.3 (algebraic functions, via Puiseux expansions) |
| 1978 | 90–95% | The omitted degree calculation behind the reported pair (40, 1380) |
| 1980 | retained numbered scope covered | Theorem 5 and unproved reported table values are excluded by the project owner; see the scope statement below |
| 1982 | 85–90% | The universal pairs of Theorem 4 with fewer than forty unknowns |
| 1984 | 85–90% | The NP characterizations (53), (54), which rest on Adleman–Manders |

For planning, reserve **roughly 10–20% of the eventual formalization effort**
for the remaining work, which no longer consists of the papers' own
constructions: what is left rests on external theories not available here
(a bridge to Mathlib's computability, Puiseux expansions for algebraic
functions, Adleman–Manders on bounded exponentiation), on exhaustive
machine searches, or on elimination calculations the editions themselves
decline to certify. This estimate is not a time forecast and
should be revised as those constructions are formalized. The theorem
tables and dated validation receipts below take precedence over these
approximate percentages.

## Shared (`Diophantine/Common/`)

| `ψ` residues mod `χ_n`: reflection, `χ_n ∣ ψ_{2n+m} + ψ_m`, period `4n`, distinctness, `ψ_i + ψ_j ≢ 0`, `ψ_j ≡ ψ_i → j ≡ ±i (mod 2n)` | `Diophantine.yn_reflect`, `xn_dvd_yn_two_mul_add`, `yn_modEq_four_mul_add`, `eq_zero_of_xn_dvd_yn_add`, `yn_modEq_cases` | proved (`PellMod.lean`) |
| every `m > 0` divides some `ψ_a(t)`, `t ≥ 1` (pigeonhole); coprime factor of a square is a square; `n < ψ_a(n)` for `n ≥ 2` | `exists_dvd_yn`, `IsSquare.of_coprime_mul`, `lt_yn_of_two_le` | proved |


| Statement | Lean name | Status |
|---|---|---|
| 1976 Lemma 2.1 = 1982 Lemma 2.19, `(2a-1)^n ≤ ψ_a(n+1) ≤ (2a)^n` | `Diophantine.pow_le_ψ_succ`, `ψ_succ_le_pow` | proved |
| 1976 Lemma 2.2 = 1982 Lemma 2.20, `ψ_a(n) ≡ n (mod a-1)` | `Diophantine.ψ_modEq` | Mathlib (`Pell.yn_modEq_a_sub_one`) |
| 1976 Lemma 2.4, congruence `χ ≡ p^n + ψ(a-p) (mod 2ap-p²-1)` | `Diophantine.χ_modEq_pow` | proved (from `Pell.x_sub_y_dvd_pow`) |
| 1976 Lemma 2.4, inequality `p^n + ψ(a-p) ≤ χ` when `p^n < a` | `Diophantine.pow_add_ψ_le_χ` | proved |
| Pell equation `χ² = (a²-1)ψ² + 1`, `χ > (a-1)ψ` | `Diophantine.χ_sq`, `χ_gt` | proved |
| Mathlib polynomial functions are precisely evaluations of integer multivariate polynomials, with arbitrary variable types | `Diophantine.isPoly_eval_mvPolynomial`, `isPoly_iff_exists_mvPolynomial` | proved (`MathlibPolynomial.lean`) |
| Arbitrarily indexed witnesses reduce to finite polynomial support; Mathlib `Dioph` is equivalent to a polynomial with `Fin m` witnesses | `Diophantine.exists_fin_witness_polynomial`, `dioph_iff_exists_fin_polynomial` | proved (`MathlibDiophFinite.lean`); input coordinates are unchanged and may form an infinite type; the latter interface uses `α : Type` for universe matching |
| A function with a Diophantine graph has a finite-witness integer polynomial whose positive values at each fixed input are exactly its positive output | `Diophantine.exists_polynomial_of_dioph_graph` | proved (`DiophantineFunctionPolynomial.lean`); Putnam's construction adds the output as one witness and gives no numerical witness bound |
| Diophantine functions are closed under Mathlib natural pairing and both inverse projections | `Diophantine.pair_dioph`, `unpair_left_dioph`, `unpair_right_dioph` | proved (`DiophantinePairing.lean`); two polynomial branches and existential inverse graphs, including zero and equal-input cases |
| Bounded universal quantification, exact iteration, and finite reachability preserve Diophantineness under Diophantine substitutions | `Diophantine.boundedForall_dioph`, `exactIter_dioph`, `existsExactIter_dioph` | proved (`DiophantineTrace.lean`); all five cipher closure contracts are discharged by the twelve vendored `PAListCoding` proof modules |
| Primitive-recursive functions have Diophantine graphs and preserve arbitrary Diophantine input substitutions | `Diophantine.natPrimrec_dioph_comp`, `natPrimrec_dioph` | proved (`PrimitiveRecursiveDioph.lean`); scalar adapters to `MRDP.primrec_diophFn` in `MRDPCore.lean`, whose CRT and beta-coded traces include zero-length recursion |
| Every recursively enumerable natural predicate is Diophantine | `Diophantine.rePred_dioph` | proved (`RecursivelyEnumerableDioph.lean`); adapts the finite polynomial from `MRDP.mrdp` to Mathlib `Dioph`; all natural inputs including zero; the scalar `encoded_evaln_natPrimrec` interface is retained independently |
| MRDP: an r.e. natural set has one integer polynomial with finitely many natural witnesses, uniformly for all inputs; converse and full equivalence | `Diophantine.mrdp`, `mrdp_iff`, `mrdp_dioph_iff`, `finite_polynomial_rePred`, `dioph_rePred` | proved (`MRDP.lean`, `Common/MRDPCore.lean`, `DiophantineEnumerable.lean`); the concise forward proof uses Mathlib alone, and the established converse is retained; all natural inputs, including zero; [proof guide](MRDP.md) |
| Matijasevič–Robinson relation combining: any finite family of integer squares, one divisibility with nonzero divisor, and strict positivity are equivalent to one polynomial equation with one new natural witness | `Diophantine.RelationCombining.relationCombining_iff` | proved (`RelationCombining.lean`); signed radicands, repeated square classes, zero roots, and the empty family are included; no project axiom |
| Ordinary joint relation-combining polynomial and substitution into arbitrary integer polynomials | `Diophantine.RelationCombiningPolynomial.polynomial`, `eval_polynomial_assignment`, `compose`, `eval_compose` | proved (`RelationCombiningPolynomial.lean`, `RelationCombiningComposition.lean`); sign invariance and explicit exponent halving remove the formal radicals |
| Refined relation combining with individual weights, positive divisor, and nonnegative dividend | `Diophantine.RefinedRelationCombining.relationCombining_iff`, `RefinedRelationCombiningPolynomial.value_eq_product`, `compose`, `eval_compose` | proved; includes signed and repeated radicands, zero roots, and the empty family |
| Degree calculus for arbitrary polynomial substitutions, including polynomial coefficient degrees and halved radical exponents | `Diophantine.RefinedRelationCombiningPolynomial.totalDegree_compose_le`, `totalDegree_compose_six_le`, `totalDegree_compose_five_le` | proved (`RefinedRelationCombiningDegree.lean`); the numerical combined-equation bounds are 13376 and 6848 |

## 1976 — Diophantine Representation of the Set of Prime Numbers

| Statement | Lean name | Status |
|---|---|---|
| Lemma 2.3, size bound `e-1+e^(e-2) ≤ n` | `JSWW1976.lemma_2_3` | proved |
| Lemma 2.3, converse (solutions with `t ∣ n+1`) | `JSWW1976.lemma_2_3_converse` | proved (Mathlib's general Pell theorem) |
| Lemma 2.5 / Corollary 2.6 (Diophantine definition of ψ, 5 unknowns) | `JSWW1976.corollary_2_6` | proved (from `Pell.matiyasevic`) |
| Lemma 2.7 (Bernoulli) | `JSWW1976.lemma_2_7` | proved (Mathlib `one_add_mul_le_pow`) |
| Lemma 2.8 | `JSWW1976.lemma_2_8` | proved |
| Lemma 2.9 (Wilson) | `JSWW1976.lemma_2_9` | proved (Mathlib `Nat.prime_iff_fac_equiv_neg_one`) |
| Lemma 2.10 (factorial via binomial remainder), incl. (i)–(iv) | `JSWW1976.lemma_2_10`, `lemma_2_10_iv` | proved |
| Lemma 2.11 (factorial from three exponentials) | `JSWW1976.lemma_2_11` | proved |
| Theorem 2.12 (`k+1` prime ⟺ system (1)–(14) solvable) | `JSWW1976.theorem_2_12` | proved |
| Theorem 1 (positive values of polynomial (1) are exactly the primes) | `JSWW1976.theorem_1` | proved |
| Theorem 2 (12-variable polynomial), §3 (Theorem 3.9) | `JSWW1976.ExactDegreePrimePolynomial.exists_exact_degree_prime_polynomial`, `theorem_3_9` | proved, including exact degree 13697; the exact-degree construction uses positive padding |
| Theorem 3: the exact range of `2 + k * 0^M` is the primes, with a nonnegative integer polynomial and eleven auxiliary natural variables | `JSWW1976.PrimeZeroTest.theorem_3`, `prime_iff_parameter_witnesses` | proved (`PrimeZeroTest.lean`); successful tests return `k+2`, failed tests return 2, and `0^0=1` is explicit |
| Theorem 4: one finite-witness integer polynomial has the nth prime as its only positive value at each fixed positive input | `JSWW1976.nthPrime_graph_dioph`, `theorem_4` | proved (`NthPrimeGraph.lean`, `NthPrimePolynomial.lean`); one-based input uses `Nat.nth Nat.Prime (n - 1)`; the further fourteen-witness bound is not asserted |
| Theorem 5: 87-operation primality certificate | `JSWW1976.theorem_5`, `PrimalityCertificate.prime_iff_certificate`, `check_counts` | proved (`PrimalityCertificate.lean`); 40 addition checks and 47 multiplication checks, signed intermediates, all natural candidates including prime 2; equality/domain tests and fixed numerals are uncharged |

Formalization notes: equations with subtraction are stated over `ℤ` with the
natural unknowns cast (`Cor26System`, `Thm212System`), because the article's
equations are integer identities; truncated `ℕ` subtraction would weaken
Corollary 2.6 (see the docstring in `Cor26.lean`).

| §3 Lemmas 3.1, 3.2, 3.5, 3.6 (real estimates), Weierstrass product inequality | `JSWW1976.lemma_3_1`, `lemma_3_2`, `lemma_3_5`, `lemma_3_6`, `one_sub_sum_le_prod_one_sub'` | proved (`Ineq3.lean`) |
| §3 Lemma 3.3 (`⌊(x+1)^n/x^k⌋ = C(n,k) + wx`, `w ≥ 1`, fractional part `< 1/8`) | `JSWW1976.binomial_split`, `lemma_3_3` | proved |
| §3 Lemma 3.4 (`n^k/C(n,k) ≤ k!(1 + 2(k−1)²/n)`) | `JSWW1976.lemma_3_4` | proved |
| §3 Definition 3.7 (`U(x,y)`; `U = □ → x^x < y`; large `y` exist) | `JSWW1976.U`, `lt_of_U_square`, `exists_U_square` | proved |
| §3 Lemma 3.8 (Matijasevič–Robinson system (A1)–(A7) for `ψ_A(B) = C`), both directions | `JSWW1976.lemma_3_8`, `MRSystem` | proved (`MR.lean`; not an axiom) |
| §3 Theorem 3.9: the system (I)–(XXI) (`Sys39`, (XIV) over `ℝ` with explicit definedness), bounds (2)–(5), estimate (11) for `σ` | `JSWW1976.Sys39`, `basic_bounds`, `sigma_estimate` | proved (`Theorem39.lean`) |
| §3 Theorem 3.9: Case 1 congruence (12)–(15), (19): `0 < σ−(w+1)x < x → |σ−(w+1)x−C(n,k)| < 1/4` | `JSWW1976.case1_congruence` | proved (`Theorem39b.lean`) |
| §3 Theorem 3.9: `β` estimates (20), (21) with the side conditions (i)–(iv) (`5k! ≤ C(n,k)`, `20k!(k−1)² ≤ n`, …) | `JSWW1976.beta_upper`, `beta_lower`, `five_factorial_le_choose`, `twenty_factorial_le` | proved |
| §3 Theorem 3.9: (17) `R/C < 1/(2Mx)²`; `σ < 1/2` when an index `p'`, `l'` is off; `β < 1/2` when `r'` is off (`R > C³`) or in Case 2; packaged `|β − k!| < 1/2` | `JSWW1976.rho_bound`, `sigma_small`, `beta_lt_half_of_large_R`, `case2_bound`, `beta_estimate` | proved (`Theorem39c.lean`) |
| **§3 Theorem 3.9**: `k+1` prime ↔ (I)–(XXI) solvable, both directions | `JSWW1976.theorem_3_9` (`theorem_3_9_sufficiency`, `theorem_3_9_necessity`) | proved (`Theorem39d.lean`) |
| §3 Theorem 3.9: eliminate fourteen capital letters to six square tests, one divisibility, and one positive polynomial margin in ten natural witnesses | `JSWW1976.theorem_3_9_reduced`, `reducedSys39_iff_exists_sys39`, `beta_defined_iff_margin` | proved (`Theorem39Elimination.lean`); the strict margin retains both denominator conditions, and the divisor is positive on every natural assignment |
| Theorem 2, original twelve-variable existence: an explicit ordinary integer polynomial has exactly the primes as its positive values on natural assignments | `JSWW1976.TwelveVariable.primePolynomial`, `prime_iff_positive_value`, `exists_twelve_variable_prime_polynomial` | proved (`TwelveVariablePolynomial.lean`); `MvPolynomial (Fin 12) ℤ`, includes prime 2, uses all six original square tests |
| Theorem 3.9 with its two growth assumptions exposed, including construction of the remaining witnesses for supplied `n,x` | `JSWW1976.theorem_3_9_sufficiency_of_growth`, `theorem_3_9_necessity_of_growth`, `reducedGrowthSys39_iff_exists_growthSys39` | proved (`Theorem39d.lean`, `Theorem39Elimination.lean`) |
| Polynomial majorants for six and five radicands, valid on every natural assignment | `JSWW1976.RefinedWeightBounds.weights_majorant`, `fiveWeights_majorant` | proved (`RefinedWeightBounds.lean`); bounds include signed `K,L,R,G` and do not assume the prime criterion |
| Equation (24), its coprime factors, Pell growth, and the five-square prime criterion with ten natural witnesses | `JSWW1976.fiveSquareRadicand_growth`, `exists_fiveSquareRadicand_square`, `theorem_3_9_five_square` | proved (`FiveSquareGrowth.lean`, `FiveSquareCriterion.lean`); does not assert the original second square test |
| Refined six-square and five-square prime polynomials on twelve natural coordinates | `JSWW1976.RefinedTwelveVariable.prime_iff_positive_value`, `FiveSquarePrimePolynomial.prime_iff_positive_value` | proved; both include prime 2 and use one combining witness |
| Unpadded refined degree bounds: six-square combined/prime polynomials at most 13376/26753; five-square counterparts at most 6848/13697 | `JSWW1976.RefinedPolynomialDegrees.totalDegree_six_combined`, `totalDegree_six_primePolynomial`, `totalDegree_five_combined`, `totalDegree_five_primePolynomial` | proved (`RefinedPolynomialDegrees.lean`); no exact-degree claim for the unpadded combined polynomials |
| Theorem 2, literal exact-degree existence: a polynomial on `Fin 12` has degree 13697 and exactly the primes as its positive natural-assignment values | `JSWW1976.ExactDegreePrimePolynomial.totalDegree_primePolynomial`, `prime_iff_positive_value`, `exists_exact_degree_prime_polynomial` | proved (`ExactDegreePrimePolynomial.lean`); a positive padding factor preserves the natural zero set and adds no coordinate |
| §4 Theorem 4.1: a complex polynomial taking only prime values on the nonnegative integer grid is constant | `JSWW1976.prime_values_polynomial_constant`, `theorem_4_1` | proved (`PrimePolynomialConstant.lean`); rational descent, positive denominator clearing, and constancy on an infinite progression grid; all finite arities including zero |
| §4 Theorem 4.4: an exponential polynomial `Σ Pᵢ(x) aᵢ^{Qᵢ(x)}` (integer `Pᵢ, Qᵢ`, `Qᵢ ≥ 0` on the grid, `aᵢ > 0`) taking only prime values on `ℕⁿ` is constant there, and its real extension is constant on `ℝⁿ` | `JSWW1976.theorem_4_4`, `theorem_4_4_real`, `line_constant`, `Diophantine.expPoly_eq_zero_of_frequently` | proved (`ExpPrimeConstant.lean`, `Common/ExpPolyZeros.lean`); Fermat along `x₁ + kp(p−1)` or a repeated bounded value, then the dominant-term argument |
| Theorem 4's refinement to fourteen witnesses | `JSWW1976.theorem_4_fourteen`, `nthPrime_graph_nine`, `pairCode_injective` | proved (`NthPrimeFourteen.lean`), via the 1982 nine-unknown reduction applied to the codes `(n+m)² + 3m + n + 1` of the graph |
| §4 Theorem 4.2 and Corollary 4.3 (algebraic functions) | | not yet formalized |

## 1984 — Register machine proof (`Diophantine/Paper1984/`)

| Statement | Lean name | Status |
|---|---|---|
| Definition of `≼` (bitwise) | `JM1984.Mask` | defined |
| (10) `a ≼ b ↔ a & b = a` | `JM1984.mask_iff_land` | proved |
| (12) `a pow 2 ↔ 0 < a ∧ a ≼ 2a-1` | `JM1984.pow_two_iff_mask` | proved |
| Lemma (Lucas): `r ≼ s ↔ C(s,r)` odd | `JM1984.mask_iff_choose_odd` | proved (Mathlib's Lucas theorem) |
| (8) `m = C(n,k)` via base-`u` digits of `(u+1)^n` (any `u > 2^n`, `k ≤ n`) | `JM1984.choose_eq_iff_digits` | proved |
| (9) `rem(2^(xy²), 2^(xy) − x) = x^y` for `y > 1` | `JM1984.rem_two_pow_eq_pow` | proved |
| (11) `a & b = c ↔ c ≼ b ∧ b ≼ a+b−c` | `JM1984.land_eq_iff_mask` | proved (digit induction, `add_eq_land_add_lor`) |
| (13) `a ≼ b ∧ c ≼ d ↔ a+cQ ≼ b+dQ` (`Q` pow 2, `a,b < Q`) | `JM1984.mask_add_pow_two_mul` | proved |
| Base-`Q` blocks: digits, injectivity, blockwise `≼` (from (13)), carries | `JM1984.blocks`, `digit_blocks`, `blocks_eq_iff`, `mask_blocks_iff`, `blocks_normal`, `carry_le_one'` | proved (`Blocks.lean`) |
| §3 register machines: commands (15)–(19), parallel updates, semantics, `Accepts`, well-formedness | `JM1984.RM.Cmd`, `step`, `run`, `Accepts`, `WF`, `regs_run_le` | defined (`Machine.lean`) |
| Conditions (35)–(37) read blockwise, with carries (`Q L_i ≼ L_n + QI + 2U − 2V`) | `JM1984.compare_cond` | proved (`Compare.lean`) |
| The system (24)–(39): `JM1984.RM.Sys` (operand histories `0`/`I`, register equations with the subtracted sum on the left) | `Sys`, `lineCond`, `regEq` | defined (`Encoding.lean`) |
| §3 completeness: `Accepts P x → ∃ s Q I R L, Sys …` with `Q = 2^(x+s+l+2)` | `JM1984.RM.sys_of_accepts` | proved (`Completeness.lean`) |
| §3 soundness: `Sys … → Accepts P x` (blocks read off, computation reconstructed by induction on `t`) | `JM1984.RM.accepts_of_sys` | proved (`Soundness.lean`) |
| **§3 main theorem**: `Accepts P x ↔ ∃ s Q I R L, Sys P x s Q I R L` for well-formed `P` | `JM1984.RM.accepts_iff` | proved (`Theorem.lean`) |
| §4: the fast commands (41) `Ri ← Ri + Rj`, (42) `Rj ← ⌈Rj/2⌉`; the macros `R ← 0` (with the conditional decrement), the even test (44) via (43), the quotient `⌊R/2⌋`, and the multiplication (45), each with a logarithmic step bound; the masking conditions (47) ⟺ (48), (49) ⟺ (50) (with the corrected term `L_p`), and (52) for `BRANCH` with distinct targets | `JM1984.RM.XCmd`, `zero_macro`, `even_macro`, `quot_macro`, `mul_macro`, `JM1984.mask47_iff`, `mask49_iff`, `branch_iff`, `even_iff_two_mul_ceil` | proved (`FastMachine.lean`, `FastMasks.lean`) |
| **§4 main theorem**: the extended system (46)–(50) for programs with the fast commands (`XSys`: (46) `2·2^s(x+1) < Q`, a fall-through condition for every fast line, the unknowns `M_n`, `J_p` with (47)/(49), and the register equations with the extra terms `QM_n`, `−QJ_p`); an accepting run solves it, and every solution is the accepting run (the blocks of `M_n`, `J_p` are `r_{k,t}l_{n,t}`, `⌊r_{j,t}/2⌋l_{p,t}`, and a step at most doubles a register, so `r_{j,t} < 2^t(x+1)`) | `JM1984.RM.XSys`, `xsys_of_accepts`, `xrun_of_xsys`, `xaccepts_iff` | proved (`FastSystem.lean`, `FastSoundness.lean`) |
| **§5, the nondeterministic command (51)**: machines whose runs are guided by a sequence of choices `ch : ℕ → Bool`, `BRANCH (Li, Lj)` transferring to `Li` or `Lj`; the system of §4 with (52) `Q L_n ≼ L_i + L_j` for a branch line with distinct targets (and `Q L_n ≼ L_i` when `i = j`); acceptance by some sequence of choices is equivalent to solvability | `JM1984.RM.NCmd`, `nstep`, `nrun`, `NAccepts`, `NSys`, `nsys_of_accepts`, `naccepts_of_nsys`, `naccepts_iff` | proved (`NDet.lean`) |
| §4–§5: polynomial-time equivalence with Turing machines (cited from Minsky) and the NP characterizations (53), (54) (using Adleman–Manders) | | not yet formalized |
| Normalisation (after (32)–(33)): unique final STOP, trampolines for self-targeting conditional jumps, next-line conditional jumps as GO TO, a dead loop for jumps outside the program; the normalized program is well formed and accepts exactly the inputs on which the raw program reaches a STOP with all registers zero; hence the arithmetization for raw programs | `JM1984.RM.normalize`, `normalize_wf`, `accepts_normalize_iff`, `acceptsStop_iff` | proved (`Normalize.lean`) |
| §2 translation: singlefold unary exponential Diophantine representations (terms with `+`, `·`, `2^·`), closure under conjunction, substitution and existential quantification over determined values, one equation `Σ(lᵢ²+rᵢ²) = Σ2lᵢrᵢ`; order (3), two-place powers by (9), masking by (8), Lucas' lemma and the shift `4a+3 ≼ 4b+3` | `JM1984.Exp.UTerm`, `SFU`, `SFU.and`, `SFU.subst`, `SFU.exists_unique`, `SFU.single_equation`, `SFU.lt`, `SFU.le`, `SFU.pow`, `SFU.mask` | proved (`ExpDioph.lean`, `ExpPrim.lean`) |
| (24)–(39) with the base fixed as `Q = 2^{x+s+l+2}` translated into unary exponential equations; the translation is faithful (`expCond_iff`, removing truncated subtraction by the bound `2·enc ≤ QI`), solutions are unique (`sysQ_unique`, from the canonical digits `sys_canonical`); acceptance by a well-formed program is singlefold unary exponential Diophantine | `JM1984.RM.ExpCond`, `expCond_sfu`, `expCond_iff`, `sys_canonical`, `sysQ_unique`, `accepts_sfu` | proved (`ExpSys.lean`, `Soundness.lean`) |
| **The paper's theorem**: every recursively enumerable set is singlefold unary exponential Diophantine, as one equation, and in the form (1) with general exponentiation; three-counter programs compiled into register machines (three lines per instruction) | `JM1984.RM.ofCounter`, `acceptsStop_ofCounter`, `acceptsStop_sfu`, `re_sfu`, `re_single_equation`, `re_exp_diophantine` | proved (`DPR.lean`); relations of several arguments are sets of codes (not separately stated) |
| §4–§5 | | — |

## 1974 — Recursive undecidability (`Diophantine/Paper1974/`)

| Statement | Lean name | Status |
|---|---|---|
| Two-symbol Turing machines (cards, states `1..n` as `Fin n`, halting state `none`), `step`, `run`; the unary I/O convention (`x` ↦ `x+1` ones, scanned at the leftmost), `Computes`, `TMComputable`; blank-tape halting and the score; shift invariance; sequential composition `seq N M` with `Computes N g → Computes M f → Computes (seq N M) (f ∘ g)` | `Jones1974.Machine`, `Computes`, `HaltsWithScore`, `seq`, `computes_seq`, `prints_seq` | proved (`Machine.lean`) |
| The printers `M^(x)` (`x+1` states, `x ≥ 1`) and a 3-state successor machine, verified step by step | `Jones1974.printer_prints`, `succ1_computes` | proved (`Printer.lean`) |
| Example 2: the 5-state machine computes `f(x) = 2x` (stage invariant `S_i`, sweeping lemmas) | `Jones1974.doubler_computes` | proved (`Doubler.lean`) |
| `Σ(n)` (largest score of a halting `n`-state machine), `Σ(n) ≤ Σ(n+1)` by padding, `Σ(n) < Σ(n+1)` for `n ≥ 1` by the paper's extra card | `Jones1974.sigma`, `sigma_mono`, `sigma_lt_succ` | proved (`Sigma.lean`, `More.lean`) |
| Theorem 1: `f` monotone and computed by a `c`-state machine ⇒ `f(n) < Σ(n)` for `n ≥ 12 + 2c` (composite machine `M^(x)` → doubler → `M`, and with the successor machine for the odd arguments) | `Jones1974.theorem_1` | proved (`Sigma.lean`) |
| Corollary 1: for every Turing computable `f` there is `N` with `f(n) < Σ(n)` for `n ≥ N`; hence `Σ` is not Turing computable, and no computable `f` satisfies `Σ(n) ≤ f(n)` for all `n` | `Jones1974.corollary_1`, `sigma_not_computable`, `no_computable_bound` | proved (`Sigma.lean`; proved directly from Theorem 1 with `N = 17 + 2c` via the successor machine, instead of through Kleene's `f̂`) |
| `SH(n)` (maximal number of shifts), `SC(n)` (maximal number of squares scanned), `Σ(n) ≤ SC(n) ≤ SH(n)`, neither `SC` nor `SH` is Turing computable | `Jones1974.SH`, `SC`, `sigma_le_SC`, `SC_le_SH`, `SC_not_computable`, `SH_not_computable` | proved (`Sigma.lean`, `More.lean`) |
| Theorem 2 (the Turing machine game): player II wins with `f` iff `SH(n) ≤ f(n)` for all `n`; `SH` is a winning strategy; no computable strategy wins for II; no strategy `g ≥ 1` wins for I | `Jones1974.winningII_iff`, `SH_winning`, `no_computable_winningII`, `no_winningI` | proved (`Sigma.lean`) |
| `H(n)` (number of halting `n`-state machines), `H(n) < (4n+4)^{2n}` (the paper's (2)) | `Jones1974.H`, `card_machine`, `H_lt` | proved (`More.lean`); the paper's informal dovetailing argument that `H` is not computable is not formalized |
| `L_n = 4(4n+4)^{2n-1} ≤ H(n)`, `U_n < L_{n+1}`, `H` strictly increasing; the paper's (4) `SH(n) ≤ n·SC(n)·2^SC(n)`; the table's first row `Σ(1) = SC(1) = SH(1) = 1`, `H(1) = 32` | `Jones1974.L_le_H`, `U_lt_L`, `H_strictMono`, `H_mem_interval`, `SH_le`, `table_one` | proved (`Counting.lean`) |
| **(3) `SC(n) < Σ(3n)`** (`n ≥ 1`): the editorial construction — `M` is simulated on the even squares by `n` states `A q`, the `2n` helper slots `B (q, d)` write a one on each crossed edge (one slot is free, since a halting machine has a halting rule, and is used as the final state `Z`), the halting rule writes a one on the last data square, and `Z` runs right over the ones and appends one more; the `k` actively scanned squares inject into the ones of the final tape, so the score exceeds `k` | `Jones1974.sc_lt_sigma`, `double`, `sim`, `z_run`, `edgeOf_injOn`, `exists_SC_witness`, `exists_missing` | proved (`Doubling.lean`) |
| Computability claims about `H` (not computable, retraceable/immune range, `{(m,n): m ≤ H(n)}` r.e. nonrecursive), degrees `0'`, hyperimmunity of `ran Σ`, growth `f(Σ(n)) < Σ(n+1)` i.o.; the upper halves of the table rows `n = 2, 3` (exhaustive search over all 2- and 3-state machines) and the counts `H(2)`, `H(3)`; the rows `n ≥ 7` | | not yet formalized |
| The table, rows `n = 2, 3, 4, 5, 6`: explicit machines checked by kernel evaluation — `n = 2` (`1RB 1LB / 1LA 1RH`) gives `Σ(2) ≥ 4`, `SC(2) ≥ 4`, `SH(2) ≥ 6`; `n = 3` gives `Σ(3) ≥ 6`, `SC(3) ≥ 7`, `SH(3) ≥ 21` (three machines); `n = 4` (`1RB 1LB / 1LA 0LC / 1RH 1LD / 1RD 0RA`) gives `Σ(4) ≥ 13`, `SC(4) ≥ 14`, `SH(4) ≥ 107`; `n = 5` gives `Σ(5) ≥ 16` (21 ones in 218 shifts); `n = 6` gives `Σ(6) ≥ 35` and `SH(6) ≥ 436` (36 ones in 570 shifts) | `Jones1974.table_two`, `table_three`, `table_four`, `table_five`, `table_six`, `ncard_ones_eq`, `ncard_scanned_eq` | proved (`TableBounds.lean`) |

## 1978 — Three universal representations (`Diophantine/Paper1978/`)

| Statement | Lean name | Status |
|---|---|---|
| The Cantor pairing `J`, `K`, `L`: `2J(s,w) = (s+w)² + 3w + s`, `J(K(y), L(y)) = y`, `J` injective, `K(y), L(y) ≤ y` | `Jones1978.J`, `two_J`, `J_K_L`, `J_injective`, `J_eq_iff`, `K_le`, `L_le` | proved (`Pairing.lean`) |
| Lemma 2.1 (`u ∣ v ∧ 0 < w ↔ ∃ t, uvw = v + tu`), Lemma 2.2 (Matijasevič's version for integers) | `Jones1978.lemma_2_1`, `lemma_2_2` | proved (`Combining.lean`) |
| The Divisor Lemma: `s ∣ t₁⋯tₙ ⇒ ∃ p, i, p ∣ s, p ∣ tᵢ, s ≤ pⁿ` | `Jones1978.divisor_lemma` | proved (`Combining.lean`) |
| Lemma 2.3, the Bounded Quantifier Theorem, both directions, for any congruence-preserving `P : ℕ → (Fin (m+1) → ℕ) → ℤ` with a dominating function `R` | `Jones1978.bqt`, `bqt_sufficiency`, `bqt_necessity`, `BQTConds` | proved (`BQT.lean`) |
| Lemma 2.4 (`J³(J+2)(r+1)² + 1 = □ ⇒ J − 1 + J^(J−2) ≤ r`, and the converse with `z ∣ r + 1`) | `JSWW1976.lemma_2_3`, `lemma_2_3_converse` | proved (shared with 1976, `Paper1976/Lemma23.lean`) |
| Lemma 2.5 (`a ≡ b (mod d) ⇒ C(a,z) ≡ C(b,z) (mod d/(d,z!))`), Lemma 2.6 (`⌊(X+1)^N/X^z⌋ ≡ C(N,z) (mod X)` for `z < N`, `N^z < X`) | `Jones1978.lemma_2_5`, `lemma_2_6` | proved (`Binomial.lean`) |
| Lemma 2.7: for `z! + 6 < r`, `z! ∣ r + 1`, U0 ⟺ B0–B8 are satisfiable; B0–B8 also give `z < N`, `1 < Y`, `8N^z < X` | `Jones1978.lemma_2_7`, `lemma_2_7_of_B`, `exists_B_of_U0`, `BConds`, `U0` | proved (`Lemma27.lean`) |
| Lemma 2.8 (Matijasevič–Robinson): for `0 < Y`, `4N^Z < X`, `0 < Z < N`, `Y = ⌊(X+1)^N/X^Z⌋ ⟺ T0–T9`, and T4–T9 give `A, B, C, K, L, M > 1`; the variant with `5(C−KLY)² ≤ K²L²` and `M = 9NXY` (for `1 < Y`, `8N^Z < X`), stated without proof and used in (1.3) | `Jones1978.lemma_2_8`, `lemma_2_8'`, `floor_core`, `exists_core`, `TConds.gt_one` | proved (`Lemma28.lean`; cited from [20] by the article, proved here by the ratio method) |
| Lemma 2.9 (`C = ψ_A(B)` via A1–A7) | `JSWW1976.lemma_3_8` | proved (shared with 1976, `Paper1976/MR.lean`) |
| Lemma 2.10 in the form Q1–Q4 (`C = ψ_A(B)` via the `χ` step-down lemma; Q4 read over `ℤ`) | `Jones1978.lemma_2_10`, `psi_of_QConds`, `exists_QConds_of_psi` | proved (`Lemma210.lean`) |
| §3: the polynomials `Pₙ` (`P_{3i+2} = Xᵢ`, `P_{3i} = P_{K i} + P_{L i}`, `P_{3i+1} = P_{K i} P_{L i}`), the sets `Wₙ` (integer witnesses) and `Ŵₙ` (nonnegative witnesses) | `Jones1978.P`, `W`, `Wh` | defined (`Enumeration.lean`, `Godel.lean`) |
| Lemma 3.1 with the enumeration: every Diophantine set of positive integers is some `Wₙ` (Putnam's device, Lagrange's four squares, and the coding of integer polynomials without constant term as differences of two `P`'s) | `Jones1978.lemma_3_1`, `IsDiophantine`, `Term.exists_index` | proved (`Enumeration.lean`); the lemma does not use DPRM; RE completeness is supplied separately by `Jones1978.isDiophantine_of_rePred` |
| Finite-polynomial and Mathlib Diophantine definitions agree on all natural inputs; intersection, union, and fixed-base power sets | `Jones1978.isDiophantine_iff_mathlib_dioph`, `IsDiophantine.inter`, `IsDiophantine.union`, `isDiophantine_powers` | proved (`MathlibDiophBridge.lean`); includes input zero, empty witness support, and bases zero and one |
| Gödel's `S(R, β, i)` (absolutely least residue mod `1 + (1+i)β`), the coding of any integer sequence, and the least-nonnegative-residue variant `S₊` | `Jones1978.S`, `S_unique`, `exists_S_eq`, `Sp`, `exists_residues`, `coprime_one_add_mul` | proved (`Godel.lean`) |
| Lemma 3.2 (`x ∈ Wₙ ⟺ (3.2)`) | `Jones1978.lemma_3_2`, `Cond32` | proved (`Godel.lean`) |
| Theorem 1 (the prenex formula `F(x, n)` for `Ŵₙ`) and Theorem 2 (the single polynomial equation, matrix over `ℤ`), via `Thm1 ⟺ Thm2` | `Jones1978.theorem_1`, `theorem_2`, `thm1_iff_thm2` | proved (`Theorems12.lean`) |
| Lemma 3.4 (`x ∈ Wₙ ⟺ J(u,v) = n ∧ U2 ∧ U3 ∧ U4 ∧ (∀ y < 3n)(∃ b e g s w) A(y)B(y)C(y) = 0`), both directions; the necessity also with all witnesses below `3n + R³` (needed for Lemma 3.5) | `Jones1978.lemma_3_4`, `Cond34`, `Apoly`, `Bpoly`, `Cpoly`, `cond34_of_mem_bounded` | proved (`Lemma34.lean`) |
| Lemma 3.5 (`x ∈ Wₙ ⟺ U0–U8`), both directions, including the omitted estimate `|A(y)B(y)C(y)| ≤ Z⁹⁰` for `y, b, e, g, s, w < Z = 3n + R³` and the inequality `(2ZZ!Z⁹⁰)^(Z⁵) + Z ≤ Z⁶ − 1 + (Z⁶)^(Z⁶−2)` for `Z ≥ 30` | `Jones1978.lemma_3_5`, `Cond35`, `P35_dominates`, `numeric_iii`, `Bd` (`Bound.lean`) | proved (`Lemma35.lean`) |
| Theorem 3: for `x, n > 0`, `x ∈ Wₙ` iff the 36-equation system (1.3) in 67 unknowns has a solution in nonnegative integers (equations read over `ℤ`) | `Jones1978.theorem_3`, `Sys13`, `mem_of_sys13`, `sys13_of_mem` | proved (`Theorem3.lean`) |
| Corollary 1 and the operation counts 243/350: a fixed 241-instruction schedule (113 addition checks, 128 multiplication checks, calculator model) with 36 equality tests certifies `x ∈ Wₙ`; the one-equation form `∑ (Lᵢ − Rᵢ)² = 0` uses 348 ≤ 350 | `Jones1978.corollary_1`, `OperationCount.mem_W_iff_certificate`, `OperationCount.check_counts`, `OperationCount.single_check_counts`, `OperationCount.certificate_iff_single` | proved (`OperationCount.lean`, generated schedule; 149 is only a forward promise of the article) |
| The table of universal pairs: all sixteen pairs, in the stronger 1982 convention (degree counts the input; three index parameters) | `Jones1982.jones1978_pairs`, `UniversalPair`, `universalPair_mono`, `universalPair_58_4`, `universalPair_40_8`, `Pair40.wset_octic40_iff` | proved (`Pair40.lean`, `UniversalPairs.lean`): eliminating eighteen positively defined witnesses of the 58-witness quadratic system gives (40, 8), and monotonicity gives the table |
| The 40-unknown reduction of the 1978 system itself via the Relation Combining Theorem, with its degree 690 | | not formalized (the pair (40, 1380) is proved by the route above) |

## 1982 — Universal Diophantine Equation (`Diophantine/Paper1982/`)

| Statement | Lean name | Status |
|---|---|---|
| Definitions: weight `σ_B(a)` (digit sum), carries `τ_B(a,b)` (Lemma 2.12 form) | `Jones1982.σ`, `Carry`, `τ` | defined (`Carries.lean`) |
| Lemmas 2.12, 2.13 (carries via integer parts; series formula) | `Jones1982.lemma_2_12`, `lemma_2_13` | proved |
| Theorem 2.14 (Kummer, 1852): `τ_B(a,b) = v_B(C(a+b,a))` for `B` prime | `Jones1982.theorem_2_14` | proved (Mathlib `padicValNat_choose'`) |
| Lemma 2.2 `τ₂(a,b) = σ(a)+σ(b)−σ(a+b)` (additive form), Lemma 2.1 `σ(a) = τ₂(a,a)` | `Jones1982.lemma_2_2`, `lemma_2_1` | proved (Kummer + Legendre's digit-sum formula, with subadditivity of `σ`) |
| `τ₂(a,b) = 0 ⟺ a &&& b = 0 ⟺ C(a+b,a)` odd | `Jones1982.τ_two_eq_zero_iff`, `τ_two_eq_zero_iff_odd` | proved |
| Lemmas 2.3–2.8 (powers of two, scaling, block sums, `σ(N−1−a)`, `v < b ⟺ τ₂(B−b,v) = 0`, `V = 0 ⟺ τ₂(B/2+V, B/2−1) = 0`) | `Jones1982.lemma_2_3`, `lemma_2_4_σ`, `lemma_2_4_τ`, `lemma_2_5`, `lemma_2_6`, `lemma_2_7`, `lemma_2_8`, `lemma_2_8'` | proved |
| Lemma 2.9 (base-`z` digits recovered in base `B` from (i)–(iii)), both directions | `Jones1982.lemma_2_9`, `mask29`, `mask29_τ_iff` | proved (`Digits.lean`) |
| Lemmas 2.10, 2.11 (combining `τ₂` conditions blockwise; list form and the three-block form of §4) | `Jones1982.lemma_2_10`, `lemma_2_11`, `lemma_2_11_lt`, `lemma_2_11_three` | proved |
| Lemma 2.15 `n ≤ σ(R) ⟺ 2ⁿ ∣ C(2R,R)`, Lemma 2.16 `τ₂(S,T) = 0 ⟺ N² ∣ C(2R,R)` | `Jones1982.lemma_2_15`, `lemma_2_16` | proved |
| 2.17 (Bernoulli, `(1−α)⁻¹ ≤ 1+2α`), Lemmas 2.18–2.21 (Pell facts, `A ≤ 2AV − V² − 1`) | `Jones1982.ineq_2_17_a`, `ineq_2_17_b`, `lemma_2_18`, `lemma_2_19`, `lemma_2_20`, `lemma_2_21` | proved (`Exponential.lean`; 2.19, 2.20 shared with 1976) |
| Lemma 2.22 (`W = V^B ⟺ ∃ A, C`: `V^(3B) < A`, `W³ < A`, `(V²−1)WC ≡ V(W²−1)`, `C = ψ_A(B)`), both directions; the `χ`-form `D ≡ W + C(A − V)` of the remark after Lemma 2.28 | `Jones1982.lemma_2_22`, `lemma_2_22'`, `key_congruence`, `pow_of_congruence`, `pow_of_χ_congruence` | proved (cited from [8] by the article; proved from the 1976 Lemma 2.4 congruence, `V ⊥ J` and a size estimate) |
| Lemma 2.23 (`C₁ = ψ_A(B₁)` from square, congruence mod `A−1`, `C₁ ≤ C`) | `Jones1982.lemma_2_23` | proved |
| Lemma 2.24 (binomial expansion of `(U+1)^(2R)/U^R`, fractional part `< 2^(2R)/U`) | `Jones1982.lemma_2_24`, `rho_split_c` | proved (from the 1976 `binomial_split`) |
| Lemma 2.25 (`N² ∣ C(2R,R) ∧ b pow 2 ⟺ (B1)–(B14)`, for `R, N ≥ 8`, `0 < b ≤ N`, `b ≤ R`), both directions, with the size facts; and the variant with the `χ`-form congruence (used in Theorem 3, §5) | `Jones1982.lemma_2_25`, `lemma_2_25'`, `B25core`, `B25core.sizes`, `B25core.core`, `B25core.dvd`, `exists_B25core`, `ratio_core` | proved (`Ratio.lean`) |
| Lemma 2.28 (`C = ψ_A(B) ⟺ (P1)–(P7)` modulo `C`, for `1 < B ≤ C` with `2B ≤ C` or `B` odd; both forms of (P5)), Corollary 2.29 (`(Q1)–(Q3)`), both directions with positive witnesses | `Jones1982.lemma_2_28`, `PConds`, `psi_of_core`, `exists_PConds`, `corollary_2_29`, `QConds29` | proved (`Psi.lean`; parity excludes `B + t₀ = C`, while `ψ_A(t₀) ≤ 2t₀` forces the harmless case `A=B=t₀=2`, `C=4`) |
| Lemma 2.26: adding `Q = B^(B₁)` to the ratio system, both congruence forms and both replacements for (B8), with positive new witnesses and exact integer interpretations | `Jones1982.lemma_2_26`, `lemma_2_26'`, `C26Conds.integer_iff`, `C26Conds'.integer_iff` | proved (`PowerExtension.lean`) |
| Lemma 2.27: `C = ψ_A(B)` via one product-square condition `DFI = □`, for arbitrary positive `J`; the coprimality remark `F ⊥ J` | `Jones1982.lemma_2_27`, `ProductPellConds`, `ProductPellConds.coprime_J` | proved (`ProductPell.lean`); alternative square systems in the remark remain separate |
| §3–§4 coding polynomials: multinomial expansion and the coefficient of `B^L` in `−c⁴D₀` | `Jones1982.Hpoly`, `coeff_Hpoly_Lexp` and the coding lemmas | proved (`Coding.lean`, `Section4.lean`, `Master1.lean`, `Master2.lean`) |
| §4 master equivalence: normalized degree-at-most-four `P`, admissible triple (4.1), and positive `x` give `Wset P x` iff the common equations and three carry conditions have positive witnesses | `Jones1982.master`, `mem_of_USys`, `USys_of_mem`, `USys` | proved (`Master3.lean`); parameterized by the number `ν ≥ 1` of witnesses of `P` |
| (4.1): admissible coding triples exist, with `z` above any prescribed bound; all coordinates are positive for `ν ≥ 1` | `Jones1982.exists_index_above`, `exists_index`, `Index.u_pos` | proved (`Index.lean`) |
| Theorem 1: the twelve-positive-witness exponential-binomial system, with `q = b^(5^(ν+2))`; existence of one admissible triple representing all positive inputs of `P` | `Jones1982.theorem_1`, `theorem_1_representation`, `Thm1` | proved (`Theorem1.lean`); the printed exponent is the specialization `ν = 58`; the RE corollaries and universal pair are proved separately below |
| §4 packing (U18–U24): all six strict block bounds from the common equations alone; packing three carry tests into one central-binomial divisibility condition; the exact integer polynomial for `r` | `Jones1982.UEqs.packing_bounds`, `pack3_carries_iff_dvd`, `centralCode_eq_rPolynomial` | proved (`PackingBounds.lean`, `Packing.lean`) |
| Theorem 2: fourteen strictly positive witnesses and one central binomial coefficient, with `q = b^(5^(ν+2))`; `r,n ≥ 8` and `b ≤ n ≤ r` from the common equations and the polynomial for `r` | `Jones1982.theorem_2`, `Thm2`, `UEqs.packing_sizes` | proved (`Theorem2.lean`); the RE corollaries and universal pair are proved separately below |
| Theorem 3 prerequisite: `χ_A(k) > 2^k + (A−2)ψ_A(k)` and a strictly positive quotient modulo `4A−5`, for `A ≥ 3`, `k ≥ 2` | `Jones1982.two_pow_add_mul_psi_lt_chi`, `exists_positive_pell_quotient`, `exists_positive_pell_quotient_int` | proved (`PellQuotient.lean`) |
| Theorem 3: eighteen polynomial equations with twenty-eight strictly positive witnesses, including one positive coding triple for all positive inputs of the supplied normalized degree-at-most-four polynomial | `Jones1982.theorem_3`, `theorem_3_representation`, `Thm3`, `exists_ratioPolynomial`, `RatioPolynomial.sound` | proved (`Theorem3.lean`, `Theorem3Defs.lean`, `RatioPolynomialDefs.lean`, `RatioPolynomialNecessity.lean`, `RatioPolynomialSoundness.lean`); exponent parameterized by `ν ≥ 1`, with `ν = 58` giving the printed `5^60` |
| §5 (D3) prerequisite: `χ_A(L) > B^L + (A−B)ψ_A(L)` and a strictly positive quotient modulo `2AB−B²−1`, for `2 ≤ B < A` and `L ≥ 2` | `Jones1982.pow_add_mul_psi_lt_chi`, `exists_positive_pell_power_quotient`, `exists_positive_pell_power_quotient_int` | proved (`PellPowerQuotient.lean`); both the natural-number and literal integer equations are retained |
| §5 shorter polynomial: distinguished coefficient `δ! P(zs)`, absolute coefficient bound, degree `< 2L`; for degree four, the strict half-base bound and the third carry test | `Jones1982.coeff_shortHpoly_Lexp`, `abs_coeff_shortHpoly_le`, `natDegree_shortHpoly_lt`, `coeff_shortHpoly_lt`, `short_tau3_iff` | proved (`ShortCoding.lean`, `ShortDigits.lean`) |
| §5 base and witnesses: powers of two, an explicit eventual-positivity cutoff for (D8), and strictly positive transfer quotients and coding witnesses | `Jones1982.shortBase_bounds`, `shortBase_pow_two`, `exists_eval_pos_cutoff`, `exists_short_D8_cutoff`, `exists_positive_eval_witness`, `exists_shortEqs_of_digits` | proved (`ShortDefs.lean`, `ShortBase.lean`, `ShortExistence.lean`, `ShortWitnesses.lean`) |
| §5 first mask and simultaneous transfer of `l,e`, including a possible coefficient at degree `L` in `e` | `Jones1982.short_code_iff`, `ShortEqs.transfer_iff` | proved (`ShortMask.lean`, `ShortTransfer.lean`) |
| §5 shorter coding equivalence: positive witnesses, three carry tests, and the retained equations `Q = B^L`, `b = 2^w`, for `L = 5^(ν+1)` | `Jones1982.short_master`, `ShortSys` | proved (`ShortMaster.lean`); supplied normalized degree-at-most-four polynomial and admissible index, `ν ≥ 1`, `x > 0` |
| §5 (D11)–(D18): six block bounds, mixed-block packing with `N = 16zQ⁵`, and `3 < 3L ≤ B ≤ Q ≤ N ≤ R`, `N,R ≥ 8`, `b ≤ N,R` without assuming the power equation | `Jones1982.short_packing_bounds`, `short_packing_iff`, `short_packing_sizes` | proved (`ShortPackingBounds.lean`, `ShortPacking.lean`); block bounds need no carry assumption, and the size chain uses (D7) with positive `λ` |
| §5 packed shorter coding equivalence: replace the three carry tests by `N² ∣ C(2R,R)`, preserving all twelve positive witnesses and justifying the signed-to-natural mask conversions | `Jones1982.short_master_packed`, `ShortEqs.shortSys_iff_packed`, `ShortPackedSys` | proved (`ShortPackedMaster.lean`); the two power equations are retained |
| §5 Pell subsystem (D3)–(D5), (D19)–(D37): twenty-seven positive witnesses, both first-coordinate congruences, and the printed `F²−A` alternative; equivalent to central-binomial divisibility and the two power relations under the independent size chain | `Jones1982.ShortPellWitnesses`, `exists_shortPell`, `ShortPellWitnesses.sound` | proved (`ShortPellDefs.lean`, `ShortPellNecessity.lean`, `ShortPellSoundness.lean`) |
| §5 complete (D1)–(D37) system: fifty-three scalar witnesses, fifty-two positive and `D₀` signed; membership equivalence and one positive coding triple for all positive inputs of a supplied normalized degree-at-most-four polynomial | `Jones1982.ShortPolynomialWitnesses`, `short_polynomial_master`, `short_polynomial_representation`, `short_ratio_iff` | proved (`ShortPolynomialDefs.lean`, `ShortPolynomialMaster.lean`); no retained power equation or central-binomial predicate, and (D21)'s rational/integer interpretations are equivalent |
| §5 explicit degree-reduction polynomials: 58 witness variables, 46 residual equations, each of degree at most two; their sum of squares has degree at most four, counting the input, and vanishes over the integers iff every residual does | `Jones1982.ShortQuadraticVar.card`, `ShortQuadraticEquation.card`, `ShortQuadratic.residual_totalDegree_le_two`, `sumSquares_totalDegree_le_four`, `eval_sumSquares_eq_zero_iff` | proved (`ShortQuadratic.lean`); parameters `z,u,y,L` are fixed coefficients |
| §5 witness shift and normalization: add one to each of the 58 witnesses, preserve the degree bounds and evaluation semantics, and obtain a nonzero polynomial value at zero witnesses for every integer input at an admissible index | `Jones1982.ShortQuadraticExpr.degreeBound_shiftWitnesses`, `ShortQuadratic.eval_shiftedSumSquares`, `shiftedSumSquares_totalDegree_le_four`, `index_normalized`, `Index.two_mul_lt_u` | proved (`ShortQuadraticShift.lean`, `ShortQuadraticIndex.lean`); (D9) has residual `2z−u`, and `ν≥1` gives `(2z)^5≤u`, hence `2z<u`; no additional witness is introduced |
| §5 solvability-preserving substitution: the complete 53-witness system is equivalent to the 46 quadratic equations in 58 positive witnesses | `Jones1982.ShortPolynomialWitnesses.exists_positiveWitnesses`, `ShortQuadratic.PositiveWitnesses.exists_shortPolynomial`, `short_polynomial_iff_quadratic` | proved (`ShortQuadraticBridgeDefs.lean`, `ShortQuadraticNecessity.lean`, `ShortQuadraticSoundness.lean`, `ShortQuarticMaster.lean`); positive slacks and square root, signed `D₀`, and block positivity are explicit |
| §5 standard polynomial representation: one input plus 58 natural witnesses in `Fin 59`, degree at most four, normalized, with the same positive-input set as any supplied normalized quartic | `Jones1982.ShortQuadratic.quartic58`, `quartic58_totalDegree_le_four`, `wset_quartic58_iff`, `quartic58_index_normalized`, `short_quartic_master`, `short_quartic_representation` | proved (`ShortQuartic.lean`, `ShortQuarticMaster.lean`); one positive coding triple works for all positive inputs; arbitrary r.e. representation is proved separately below |
| Arbitrary-degree input reduction: each 1978 enumeration set has a finite integer quadratic gate system and an explicit normalized quartic with `6n+7` natural witnesses | `Jones1982.EnumerationQuadratic.mem_W_iff_gateSys`, `EnumerationQuartic.wset_quartic_iff`, `quartic_totalDegree_le_four`, `quartic_normalized`, `exists_normalized_quartic_representation` | proved (`EnumerationQuadratic.lean`, `EnumerationQuartic.lean`); handles enumeration index zero uniformly and uses a guard witness for normalization |
| Every Diophantine set has a normalized 58-witness quartic representation on positive inputs, without restrictions on its original degree or variable count | `Jones1982.diophantine_quartic58` | proved (`DiophantineQuartic.lean`); assumes `Jones1978.IsDiophantine`, not a recursively enumerable representation theorem |
| The same normalized 58-witness quartic representation for Mathlib Diophantine sets, including every fixed-base power set | `Jones1982.mathlib_dioph_quartic58`, `powers_quartic58` | proved (`MathlibQuartic.lean`); positive-input scope is unchanged; Mathlib supplies a proof of exponentiation's Diophantine representation |
| Every recursively enumerable set has a normalized 58-witness quartic representation | `Jones1978.isDiophantine_of_rePred`, `Jones1982.rePred_quartic58` | proved (`RecursivelyEnumerableQuartic.lean`); composes the proved computability bridge with the arbitrary-degree reduction and §5 compression; positive-input scope |
| The printed Theorems 1–3 represent every recursively enumerable set, with 12, 14, and 28 strictly positive witnesses and the exponent `5^60` | `Jones1982.rePred_printed_systems`, `rePred_theorem1_system`, `rePred_theorem2_system`, `rePred_theorem3_system` | proved (`RecursivelyEnumerableSystems.lean`); one positive coding triple works for all three systems and every positive input |
| §5 universal pair (58, 4): one joint polynomial, chosen before the recursively enumerable set, with three positive index parameters | `Jones1982.rePred_quartic58_family`, `UniversalQuartic.jointPolynomial`, `UniversalQuartic.specialize_jointPolynomial`, `universal_quartic58` | proved (`UniversalQuartic.lean`); second compression fixes `L4 58 = 5^59`; degree at most four after parameter specialization, counting the input and 58 natural witnesses; membership equivalence on positive inputs |
| §3: Matijasevič's reduction to nine unknowns — every r.e. (or Mathlib-Diophantine) set of positive integers is `{x | ∃ z₁…z₉, M(x, z) = 0}` for an integer polynomial `M` | `Jones1982.nine_unknowns`, `nine_unknowns_dioph`, `Nine.wset_iff_nine`, `Nine.reduced_of_mem`, `Nine.mem_of_reduced`, `Nine.ratio_sound`, `Nine.ratio_complete`, `Nine.polyFn_nineValue` | proved (`NineReduce.lean`, `NineRatio.lean`, `NinePoly.lean`, `NineMain.lean`, `Common/PolyFn.lean`); the coding uses §4's base `b⁵` with the ceiling `b = xy + 1 + ε` instead of §3's `βb^δ`; the unknowns are `ε, g, h, s, w, φ, i, j` and the relation-combining `n`; (B3) is stacked with the ceiling for `g` using `|C − KY| ≤ 25K/64`; the divisibility is squared so the combined divisor is positive everywhere; the degree `47216·5^ν + 9728` is not asserted |

## 1980 — Undecidable Diophantine Equations (`Diophantine/Paper1980/`)

**Current completion scope (project owner, 2026-09-14): Theorems 1–3 and
the abridged Theorem 4, retaining its proved `(58,4)` construction.**
The other fifteen reported pairs are excluded for now. Theorem 5 is
intentionally excluded because its statement is vague and imprecise.
The retained numbered results are proved under the positive-input and
admissible-code conventions. The current policy forbids new axioms.
The [statement audit](PAPER1980_AUDIT.md) records the exact quantifiers,
domains, degree convention, and exclusions.

Theorems 1–3 of the announcement are, equation for equation, Theorems 1–3
of the 1982 article with `ν = 58` (exponent `5^60`). They are not restated:
the existing names are used, and their docstrings now say so.

| Statement | Lean name | Status |
|---|---|---|
| Theorem 1 (12 unknowns, three binomial coefficients, `b = 2^w`, `q = b^(5^60)`) | `Jones1982.theorem_1` with `ν = 58` | proved (identical to 1982 Theorem 1) |
| Theorem 2 (14 unknowns, one central binomial coefficient) | `Jones1982.theorem_2` with `ν = 58` | proved (identical to 1982 Theorem 2) |
| Theorem 3 (28 unknowns, eighteen polynomial equations) | `Jones1982.theorem_3` with `ν = 58` | proved (identical to 1982 Theorem 3) |
| Remark after Theorem 1: the single parameter `v = ((zuy)² + u)² + y` (the edition's footnote: injective on positive triples) | `Jones1980.indexCode`, `indexCode_injective` | proved (`IndexCode.lean`) |
| Adjoining the code equation gives one fixed positive parameter for all three printed systems | `Jones1980.singleParameterSolvable_indexCode_iff`, `rePred_single_parameter_systems` | proved (`SingleParameter.lean`); adds three positive witnesses, giving counts 15, 17, and 31; no decoder or unchanged-count claim |
| Theorem 4, row `(58, 4)`: one joint universal polynomial has degree at most four in the input and 58 witnesses after fixing the three index parameters | `Jones1982.universal_quartic58` | proved (with `REPred` as the notion of r.e. set, positive inputs, and nonnegative witnesses) |
| Theorem 4, the other fifteen reported pairs `(38, 8)`, …, `(9, D₉)` | | excluded from the current abridged scope by the project owner; not claimed as proved |
| Supporting RE-set representation: every `REPred S` has a positive index triple such that, for positive `x`, membership in `S` is equivalent to a positive solution of Theorem 3 | `Jones1980.theorem_5` | proved (`Theorem5.lean`; composition of `rePred_quartic58`, `exists_index`, `theorem_3`); no proof-system syntax or operation count is asserted |
| Theorem 5, the count `o = 100` in the calculator model: one fixed schedule of 90 instructions (42 addition checks, 48 multiplication checks, 22 equality tests, positivity domain tests) checks membership certificates for every r.e. set via `Sys90` | `Jones1982.theorem_5_operations`, `Jones1982.OperationCount.solvable90_iff_certificate`, `printed_iff_sys90`, `check_counts` | proved (`Paper1982/OperationCount.lean`); the sign-count reading of the printed Theorem 3 system is not formalized |

The 1982 article states the same Theorem 5; `Jones1980.theorem_5` serves
both, as the module docstring records.

### The 93-operation universal system (satellite work; `Diophantine/Paper1980/*93*.lean`)

Goal (project owner, 2026-09-14): formalize the encodings of the final
straight-line certificate — the 93-operation system of round 34
(`Papers/1980/AFFINE_RADIX_95_PROOF.md`, `SHIFTED_AFFINE_94_PROOF.md`,
`FACTORED_MASK_93_PROOF.md`) — and prove that they yield a universal
Diophantine equation. **Done**: `Jones1980.universal93` (for Diophantine
sets) and `Jones1980.universal93_re` (for recursively enumerable sets) in
`Universal93.lean`: for every such set `S` there is a fixed index
`(V, H, Tindex)` with `x ∈ S ↔ Solvable93 x V H Tindex` for all `x > 0`.
The earlier `System99`, `Circuit`, `PellDoubled`, `PellExponent`,
`PellRatio` modules (99-operation system) are reused where the
parametrization is unchanged.

| Statement | Lean name | Status |
|---|---|---|
| Transcription of the 22 equations / 34 positive unknowns; every field checked against the receipt `round34_1980_factored_mask_certificate.json` by `Papers/verification/lean_sys93_transcription_check.py` (22/22) | `Jones1980.Sys93`, `Solvable93`, `Pos93` | defined (`System93.lean`, `Bootstrap93.lean`) |
| Bootstrap bounds (16)–(18) from positivity alone | `Jones1980.l_lt_q`, …, `r_bounds` | proved (`Bootstrap93.lean`) |
| Strong divisibility of `ψ`, composition of Pell parameters, components of powers of a fundamental unit, `χ_A(n) ≡ Aⁿ`, `ψ_A(n+1) ≡ (n+1)Aⁿ` | `Jones1980.yn_gcd`, `comp_xn_yn`, `pow_x_y`, `xn_yn_modEq_pow` | proved (`PellRelaxed.lean`) |
| The relaxed auxiliary norm forces an integral Pell solution (`PELL_RELAXED_AUXILIARY_PROOF.md`) | `Jones1980.relaxed_aux` | proved (`PellRelaxedMain.lean`) |
| Pell block: `c = ψ_A(J)`, `d = χ_A(J)`, `k = ψ_P(r+1)`, `U = 4^J`, `q = B^L`, `κ = ψ_A(L)`, `n² ∣ C(2r,r)`, `q`, `B` powers of two | `Jones1980.pell_block`, `PellBlock93` | proved (`Pell93.lean`) |
| Three masks ⟺ `n² ∣ C(2r,r)` (widths (2,2,4) in radix `q`), with the block bounds as hypotheses (`masks_iff_central_core`) or from the system | `Jones1980.masks_iff_central_core`, `masks_iff_central`, `r_nat` | proved (`Pack93.lean`) |
| Three-digit window arithmetic, with and without a padding carry; digits `≤ 3` force `G ≥ 0` | `Jones1980.window_digits`, `window_digits_pad`, `window_nonneg_of_small`, `window_digit_bounds` | proved (`Window93.lean`, `Window93b.lean`) |
| Canonical combined code: `θλ = mask29 B 4 (2L)`, `S₂ = ofDigits B (digits of V)`, splitting `l`, `e` | `Jones1980.theta_lam_eq_mask`, `S2_eq_ofDigits`, `split_code` | proved (`CodeDigits.lean`) |
| Bitwise masks read digit by digit in radix `2^m` | `Jones1980.land_eq_zero_iff_digits`, `τ_eq_zero_iff_digits`, `digit_zero_of_land_all_ones`, `digit_bit_clear_of_land_pow` | proved (`MaskDigits.lean`) |
| The layout (weights `vᵢ = 6·3ⁱ`, `M`, `d₀`, targets `t_j`), band separation, dummy exclusion, base-three uniqueness of the weights | `Jones1980.Layout.*`, `Jones1980.Weights.*` | proved (`Layout93.lean`, `Weights93.lean`) |
| Coefficient isolation: `[X^p](D · C²)` at the eight positions of every window (`a_{t−3} = x²`, `a_{t−1} = pad`, `a_t = row value`, the rest `0`), dummies excluded through `t_{s−1} + 2` | `Jones1980.Iso.coeff_eq_main`, `coeff_band_only`, `coeff_at_target`, `coeff_at_reset`, `coeff_at_pad`, `coeff_at_empty` | proved (`Isolation93.lean`–`Isolation93d.lean`) |
| Size bounds `|[X^p](P·Q)| ≤ D₁ · Q(1)`, geometric tail, `|[X^p](D·C_main²)| ≤ D₁ (x + Σzᵢ)²` | `Jones1980.Iso.abs_coeff_mul_le`, `tail_le`, `abs_coeff_le` | proved (`Bound93.lean`, `Sigma93.lean`) |
| The fixed index: `K`, the indicator support, the digit lists of `ℓ₀` and `e₀` and their radix values | `Jones1980.Iso.K`, `supp`, `ell0d`, `e0d`, `ofDigits_ell0d`, `ofDigits_e0d` | proved (`Index93.lean`) |
| Every coefficient of `D` lies in `{−1, 0, 1}` for valid rows; every exponent of `D` is below `K` | `Jones1980.Iso.abs_coeff_D_le_one`, `coeff_D_eq_zero_of_ge` | proved (`DValid93.lean`) |
| Radix digits of explicit sums, residues, `x ≤ 3` from `x & (2^m − 4) = 0` | `Jones1980.Iso.digit_sum`, `sum_digits`, `digit_mod_pow`, `le_three_of_land` | proved (`Digits93.lean`) |
| Reading the first mask (digits of `g` vanish off the support, bit `H₀` clear on it), `x + g = C(B)`; the third mask bounds the digits of `σ` on the support by three | `Jones1980.Iso.mask_digit`, `g_digits`, `C_eq_eval`, `sigma_digits_le_three` | proved (`Mask93.lean`) |
| `σ = Σ_{p<K} [X^p](D·C²) B^p + B^K · High` | `Jones1980.Iso.sigma_decomp` | proved (`Sigma93.lean`) |
| The window of every target: `G_j + ⌊pad_j/B⌋ ≥ 0` equals the three-digit number read at `t_j, t_j+1, t_j+2` | `Jones1980.Iso.window_residue`, `window_value` | proved (`Windows93.lean`) |
| The three unit tests force `δ = 1` (square roots of one modulo a power of two; incompatible carries `⌊5x²/B⌋`, `⌊7x²/B⌋`) | `Jones1980.unit_tests` | proved (`Unit93.lean`) |
| Compiler: row shapes over three-coordinate groups and their validity; a circuit compiled to paired rows, normalization rows, padding sets; decoding of the rows (`1 ≤ δ ≤ x`, padding sums, acceptance when `δ = 1`); the three-way split witness with bit `j_H` clear | `Jones1980.Iso.copyRow`, …, `RowStruct.valid`, `pairedRows_struct`, `decode_*`, `witness_rows` | proved (`Compile93a.lean`, `Compile93b.lean`) |
| **Sufficiency**: a positive solution at the fixed index decodes to an accepting computation | `Jones1980.Iso.sufficiency` | proved (`Decode93.lean`) |
| **Necessity**: the Pell witnesses (`J = 2r+1`, `U = 4^J`, `Y = ⌊(U+1)^{2r}/U^r⌋`, `k = ψ_P(r+1)`, `c = ψ_A(J)`, `η`, `ζ`, `h`, `κ = ψ_A(L)`, `γ`, `ρ`, `Δ`, the doubled-index witnesses with the relaxed `i`) and the coding witnesses (radix `B = 2^{j_H+1} 2^N`, three-way split digits, `l = ℓ₀(B)`, `e = e₀(B)`, `λ`, `σ`, `r`, the three masks, `n² ∣ C(2r,r)`, `t`) | `Jones1980.pell_witnesses`, `Jones1980.Iso.centralW`, `E45W`, …, `Jones1980.Iso.necessity` | proved (`NecessityPell93.lean`, `NecessityCode93a.lean`, `NecessityCode93b.lean`, `Necessity93.lean`) |
| **Universality** of the 93-operation system for Diophantine and for recursively enumerable sets | `Jones1980.universal93`, `universal93_re` | proved (`Universal93.lean`) |

All results listed as proved depend only on `propext`, `Classical.choice`,
`Quot.sound` (`.lake/ops93-axioms.log`, `.lake/u93-axioms.log`).

**Validation.** Each module compiled on its own (`lake build <module>`);
`#print axioms Jones1980.universal93` and `#print axioms
Jones1980.universal93_re` report only `propext`, `Classical.choice`,
`Quot.sound`. The full-root build is validated separately (see the
receipts below).

**Moving target.** While these modules were being written the certificate
was reduced further by the concurrent optimization work (rounds 35–45:
92, 91, 90 operations and beyond, with a redesigned coefficient index).
The formalization stays on the 93-operation system, whose encodings are
now proved universal; the version-specific modules are named `*93*`.

### The 90-operation universal system (satellite work; `Diophantine/Paper1980/*90*.lean`)

Goal (project owner, 2026-09-15): formalize the 90-operation system of round
37 (`Papers/1980/BINARY_PRODUCT_90_PROOF.md`, `BASE_TWO_PELL_90_PROOF.md`,
building on `PRODUCT_BOUND_91_PROOF.md` and `HALF_PARAMETER_PELL_92_PROOF.md`;
receipt `round37_1980_binary_product_certificate.json`) and prove it
universal. **Done**: `Jones1980.universal90` and `universal90_re` in
`Universal90.lean`: for every Diophantine (recursively enumerable) set `S`
there is a fixed index `(V, H, Tindex)` with `x ∈ S ↔ Solvable90 x V H Tindex`
for all `x > 0`.  The modules shared with the 93-operation system
(`PellRelaxed*`, `PellDoubled`, `CodeDigits`, `MaskDigits`, `Digits93`,
`Bound93`, `Window93*`, `Compile93a/b`, the generic packing core
`masks_iff_central_core`) are reused; everything specific to the binary
compiler and the base-two Pell block is new.

| Statement | Lean name | Status |
|---|---|---|
| Transcription of the 22 equations / 34 positive unknowns (no `Ω`; auxiliary `y`), checked against the round-37 receipt by `Papers/verification/lean_sys90_transcription_check.py` (22/22) | `Jones1980.Sys90`, `Solvable90`, `Pos90` | defined (`System90.lean`, `Bootstrap90.lean`) |
| Bootstrap bounds from positivity alone (`C² ≤ σ < q`, `e < q`, `S, T⁺ < q⁷`, `n ≤ r < 2n³`) | `Jones1980.Csq_le_σ90`, …, `r_bounds90` | proved (`Bootstrap90.lean`) |
| Base-two exponent block (`U = 2^J`, `q = B^L`) and ratio block for `A = a + 2` | `Jones1980.Exp90.exp_U`, `exp_q`, `Jones1980.Ratio90.k_index`, `Y_lower`, `lower_estimate`, `upper_estimate` | proved (`PellExponent90.lean`, `PellRatio90.lean`) |
| Exact binomial tail for base two: `2 Σ_{m<R} C(2R,m) + C(2R,R) = 4^R`, `(U+1)^{2R} = Q U^R + v` with `4v < U^R` once `2^{2R+1} ≤ U`; rounding `Y = ⌊(U+1)^{2r}/U^r⌋` | `Jones1980.Ratio90.two_mul_sum_choose_add`, `binomial_floor_two`, `Y_eq_floor` | proved (`PellRatio90.lean`) |
| Half-parameter block: the odd-index polynomial `Q_h` (`χ_X(2h+1) = X Q_h(X²)`), its values at `1 − A²` and `0`; the main index equals `J` (sufficiency) and the witnesses for `J ≡ 1 (mod 4)` (necessity) | `Jones1980.Qh`, `xr_odd_eq`, `Qh_eval_one_sub_sq`, `half_index`, `half_witnesses` | proved (`PellHalf90.lean`) |
| Pell block: `c = ψ_A(J)`, `d = χ_A(J)`, `k = ψ_P(r+1)`, `U = 2^J`, `q = B^L`, `κ = ψ_A(L)`, `n² ∣ C(2r,r)`, `q`, `B` powers of two | `Jones1980.pell_block90`, `PellBlock90` | proved (`Pell90.lean`) |
| Three masks ⟺ `n² ∣ C(2r,r)` from the system (radix `B = H + b + 2`) | `Jones1980.masks_iff_central90`, `r_nat90` | proved (`Pack90.lean`) |
| Base-seven weights `vᵢ = 8·7ⁱ`; monomials as multisets; the weight determines the multiset up to degree six | `Jones1980.L90.W`, `W_inj` | proved (`Weights90.lean`) |
| The layout: monomials of a row, negative monomials, helper pairs, `d₀ = 12M + 8`, targets, tested starts, helper complements, resets, padding, `D`, `C_main`, `C_dum`; validity `RowOk`, `LayoutOk`; band separation, dummy exclusion | `Jones1980.L90.terms`, `negs`, `pairs`, `starts`, `Rset`, `D`, `RowOk`, `LayoutOk`, `band_unique`, `dummy_exclusion` | proved (`Layout90.lean`) |
| Coefficients of `C²` at the weights; the helper pairs sum to the helper square | `Jones1980.L90.coeff_Cmain_sq_*`, `terms_sum_eq_val`, `pairs_sum_eq_sq` | proved (`Csq90.lean`) |
| Coefficient isolation: only one band contributes to a window; at a target `R_j + [seed] V_helper²`, at a negative position `V_helper² − x²`, at `r − 4` at least `x²`, at `t_last − 1` the padding, zero elsewhere; dummies excluded | `Jones1980.L90.coeff_band_only`, `coeff_at_target`, `coeff_at_neg`, `coeff_at_reset`, `coeff_at_pad`, `coeff_at_empty`, `coeff_eq_main` | proved (`Isolation90a.lean`, `Isolation90b.lean`) |
| Every coefficient of `D` is in `{−1, 0, 1}`; negative coefficients sit at starts, positive ones off the indicator support; support below `K`; leading term `X^{t_last − 4}`; `D(B) > 0` | `Jones1980.L90.abs_coeff_D_le_one`, `coeff_D_neg_mem_Rset`, `coeff_D_nonpos_of_mem_supp`, `coeff_D_eq_zero_of_ge`, `D_eval_pos` | proved (`DValid90.lean`, `DValid90b.lean`) |
| The fixed index: indicator support, binary digit lists of `ℓ₀` and `e₀ = ℓ₀ + D`, `e₀(B) − ℓ₀(B) = D(B)` | `Jones1980.L90.supp`, `ell0d`, `e0d`, `e0d_mem_le`, `e0_sub_ell0` | proved (`Index90.lean`) |
| The masks digit by digit: first digit `H₀ = B − 1 − b`, middle mask `θλ = mask29 B 2 (2L)` and the binary canonical code, third digit `B − 2` bounds the digits of `σ` by one | `Jones1980.L90.mask_digit`, `g_digits`, `C_eq_eval`, `S2_eq_ofDigits_two`, `sigma_digits_le_one`, `le_one_of_land` | proved (`Mask90.lean`) |
| `σ = D(B) C(B)²` and its split at `K`; coefficient bound | `Jones1980.L90.sigma_decomp`, `abs_coeff_le` | proved (`Sigma90.lean`) |
| Windows with the reset four positions below the start; the value of every start read in binary digits | `Jones1980.window_digits_pad90`, `Jones1980.L90.window_residue`, `window_value` | proved (`Window90.lean`, `Windows90.lean`) |
| The two binary unit tests `δ²`, `δ² + ⌊2x²/B⌋` force `δ = 1` | `Jones1980.L90.unit_tests90` | proved (`Unit90.lean`) |
| Compiler: seed, reverse and `x`-free normalization rows; `RowOk` from structural validity; the circuit layout (two helper groups `V₀, V₁`, helpers per row, padding group `P_X`) is a valid layout; decoding (`X = V₀`, `V₀² = δ² + δu`, `1 ≤ δ ≤ V₀`, acceptance); the witness assignment | `Jones1980.L90.seedRow`, `revRow`, `uRow90`, `rowOk_of_struct`, `layoutOk`, `decode_*`, `witness_rows90` | proved (`Compile90a.lean`, `Compile90b.lean`, `Compile90c.lean`) |
| **Sufficiency**: a positive solution at the fixed index decodes to an accepting computation (seeds, paired rows, reverses, unit tests, circuit) | `Jones1980.L90.sufficiency` | proved (`Decode90.lean`) |
| **Necessity**: Pell witnesses at `A = a + 2`, `U = 2^J`, with the half-parameter witnesses (`r` even, `J ≡ 1 (mod 4)`); coding witnesses with `σ = D(B) C(B)²`, all windows binary, `n² ∣ C(2r,r)`, `t`, and the parity `2 ∣ r` | `Jones1980.pell_witnesses90`, `Jones1980.L90.centralW`, `E45W`, `rW_even`, `necessity` | proved (`NecessityPell90.lean`, `NecessityCode90a.lean`, `NecessityCode90b.lean`, `Necessity90.lean`) |
| **Universality** of the 90-operation system | `Jones1980.universal90`, `universal90_re` | proved (`Universal90.lean`) |

`#print axioms Jones1980.universal90` and `#print axioms
Jones1980.universal90_re` report only `propext`, `Classical.choice`,
`Quot.sound` (`.lake/u90-axioms.log`).

### The alternative universal architectures (in progress; `Diophantine/Paper1980/Kernel3.lean`, `*100*`, `*91*`)

Goal (project owner, 2026-09-15): formalize the alternative Turing-complete
systems explored in `Papers/1980/EXPLORATION_*.md` — the counter-machine
family (100 operations, `EXPLORATION_STATE_TOP_DOUBLED_GRID.md`, receipt
`explore_state_top_doubled_grid.json`) and the tag-system family (91 operations,
`EXPLORATION_PRODUCT_COORDINATE_TAG.md`, receipt
`explore_product_coordinate_tag.json`).  Both share the base-three Pell kernel
of `EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md`.

| Statement | Lean name | Status |
|---|---|---|
| Ratio block for the Pell base `A = a + 3` (`k = ψ_P(r+1)`, `U^r ≤ Y`, `c/k < ξ + 1/2`) | `Jones1980.Ratio3.k_index`, `Y_lower`, `upper_estimate` | proved (`PellRatio3.lean`) |
| Exponent decoding `U = 3^J` from `d = U + ac + γ(6a+8)` by the direct congruence (no cubic size condition) | `Jones1980.Exp3.exp_U` | proved (`PellExponent3.lean`) |
| The ten-equation kernel: soundness at `D₀ ≥ 81`, `r ≥ 27`, `r < 2D₀` (`U = 3^(2r+1)`, `D₀` a power of three, `D₀ ∣ C(2r,r)`) and the positive converse for even `r` | `Jones1980.Kernel3`, `kernel3_sound`, `kernel3_witnesses` | proved (`Kernel3.lean`) |
| The unit-two ternary mask (Kummer): for `P < 3^N`, `3^N ∣ C(2P,P)` iff the unit digit is `2` and the other digits below `N` are nonzero; subtracting the repunit gives a Boolean word | `Jones1980.Ternary.ternary_mask`, `sub_rep` | proved (`TernaryMask.lean`) |
| Transcription of the 100-operation counter system (22 equations, 34 unknowns, parametric in the ROM constants), checked against the receipt by `Papers/verification/lean_sys100_transcription_check.py` (22/22) | `Jones1980.ROM100`, `Sys100`, `Solvable100` | defined (`System100.lean`) |
| Transcription of the 91-operation tag certificate (18 equations, 29 unknowns, parametric in the tag constants), checked by `lean_sys91_transcription_check.py` (18/18 in both leading branches) | `Jones1980.Tag91`, `Tag91.Ok`, `Sys91`, `Solvable91` | defined (`System91.lean`) |
| Bootstrap of the counter system: `R ≥ 8·Zon + 9`, `q ≥ R³`, `q¹² ≤ 2r < 2q¹²`; kernel conclusions (`q` a power of three, `q¹² ∣ C(2r,r)`), the ternary mask of `r` and the doubled Boolean packed word | `Jones1980.kernel_out100`, `mask100` | proved (`Bootstrap100.lean`) |
| Bootstrap of the tag certificate: integer width recovery (`C ∣ R`, `R = CA`, `Z = AH`), the marker bound `2M₁ ≤ 3kH`, positivity of the packed word in both branches, kernel conclusions and masks | `Jones1980.width_recovery91`, `kernel_out91`, `mask91` | proved (`Bootstrap91.lean`) |
| Ternary digit toolkit: digit extraction from coefficient sums, carry-free sums, the carry recurrence `dg (αX+βY) p = (α dg X p + β dg Y p + carry p) mod 3`, Boolean words, base-`q` chunk decoding of signed fields | `Jones1980.Ternary.dg_val`, `dg_add_of_le_two`, `dg_lin`, `carry_succ`, `Bool3`, `chunk_step` | proved (`TernaryDigits.lean`) |
| Normalized binary tag systems (`0 → 0`, `1 → u`, deletion `β`, halting when short), content/length transports of a step | `Jones1980.TagSys`, `TagSys.step`, `Halts`, `content_step`, `length_step` | defined/proved (`TagSystem.lean`) |
| Rows, the row-head word and its digits, `m ∣ e` from `3^m − 1 ∣ 3^e − 1`; the radix geometry of a solution (`R = 3^m`, `q = R^t`, `H = heads m t`, `A`, `D` powers of three, `3β < m`, `γ ≥ 6`) | `Jones1980.Ternary.heads`, `dg_heads`, `heads_of_head_eq`, `Jones1980.geometry91` | proved (`TagRows.lean`, `TagGeometry91.lean`) |
| The nine Boolean fields `S₀, S₁, Q, G, M₀, M₁, Ē, E, GN` of a solution: scalar bounds, the content identity `3RE = (R−K)N + R(UM₁−S₁) + K·Ninit`, `GN ≤ rep e`, greedy chunk decoding | `Jones1980.Input91`, `Fields91`, `fields91` | proved (`TagFields91.lean`) |
| The row projector: the carry automaton of `2Q + S = M`, runs from heads below the guard offset, rows `rep ℓ` / `3^ℓ`, the `A = 1` exclusion | `Jones1980.Ternary.run_structure`, `rows_of_projector`, `Q_eq_zero_of_heads_free` | proved (`TagProjector.lean`) |
| Row data of a solution: head selectors, freed guard offset, prefix support, row form of the length equation, `jZ = rep β · 3^(m−β) · H` | `Jones1980.decode91`, `S1_heads`, `Q_alpha`, `rows_QM`, `E_support`, `length_eq91`, `jZ_eq` | proved (`TagDecode91.lean`) |
| The length path: digit form of `M₀ + M₁ + 3q = Linit + D M₀ + DB M₁`, the row step (successor offset; short markers of the next row are the successor; the endpoint forces offset `1`) | `Jones1980.Ternary.path_digits`, `row_zero_marker`, `row_step` | proved (`TagPath.lean`) |
| Signed content rows: the transport invariant `Einv`, the guard chunk (Boolean discrepancy `s ≤ hK`), the prefix identity `d = p + s`, the next-guard contradiction | `Jones1980.Ternary.Einv_dvd`, `Einv_next`, `guard_chunk`, `prefix_eq`, `next_guard_contra` | proved (`TagContent.lean`) |
| **Soundness of the tag certificate**: the decoded history halts the actual tag machine (`halts_of_ctx`); every positive solution of `Sys91` at an encoded instance of a matching tag system halts it | `Jones1980.halts_of_ctx`, `Jones1980.sound91` | proved (`TagSound.lean`, `TagSound91.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
| Row sums `Σ_{i<t} f i · 3^(m i)`: bound, rows, Booleanity, parity | `Jones1980.Ternary.rowsum`, `rowsum_lt`, `row_rowsum`, `bool3_rowsum`, `rowsum_parity` | proved (`RowSum.lean`) |
| The rows of an actual run (`ℓᵢ, nᵢ, sᵢ, dᵢ, eᵢ`) and its two step relations | `Jones1980.hlen`, `hcon`, `hsel`, `hpre`, `hlen_step`, `hcon_step` | proved (`TagHistory.lean`) |
| Assembling a solution from positive outer coordinates with Boolean fields, unit digit one and even packed word | `Jones1980.assemble91` | proved (`TagAssemble.lean`) |
| **Completeness of the tag certificate**: an accepting computation halting at the single-symbol word `0`, with the startup promises and an even packed index, gives a solution of `Sys91` (the nine fields built row by row; the length equation as the telescoping of the markers `3^(m i + ℓᵢ)`; the content equation as the summed step relation; the parity of the index reduced to the contents) | `Jones1980.witness91` | proved (`TagWitness.lean`) |
| **The halting equivalence**: on the completeness domain `Sys91` is solvable exactly when the tag machine halts | `Jones1980.tag_equiv91` | proved (`TagWitness.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
| **The padded canonical witness** (zero-terminal note §3, reordered-startup note §4): the witness over a height `T ≥ t`, with the length word enlarged by a Boolean `3^(mt)·Y` below `3^(mT)` obeying the zero-edge flow; every other field extends by its fixed head or guard pattern past the halt; the index parity condition becomes `2 ∣ Σ nᵢ + (T − t) + Y + mT` | `Jones1980.rowsum_eq_of_zero`, `hsel_of_ge`, `fQ_of_ge`, `fM1_of_ge`, `hpre_of_ge`, `fTc_of_ge`, `witness91_gen` | proved (`TagPad91.lean`) |
| **The tag certificate on its completeness domain** (product-coordinate note, opening): for `β ≥ 2`, `a ≥ 2`, `β ≤ |W₀|`, `K²Lᵢ < C` and the first-zero, positive-startup and single-zero-terminal promises, `Sys91` is solvable at the encoded input exactly when the tag system halts; the width is chosen odd, the four startup coordinates are positive by the promises, and an odd canonical index is flipped by the wrapped padding `3 Σ_{i<m} (3^(m−β+1))^i` | `Jones1980.TagPromise`, `pad_eq`, `pad_parity`, `tag_iff91` | proved (`TagEquiv91.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
| **Undecidability of the encoded tag family, layer 1** (Minsky arithmetization): a three-counter program compiles to a single-register machine with multiplications and divisibility tests by `2, 3, 5` on `N = 2^a 3^b 5^c`, the accept check being `N = 1`; acceptance of `x` is reaching the accepting halt from `2^x` | `Jones1980.GProg`, `CProgram.compile`, `prime_dvd_pack`, `pack_inc`, `pack_dec`, `accepts_iff_reachesAcc` | proved (`TagGoedel91.lean`) |
| **Chunkwise reading of a tag queue** (generic tag systems with deletion `d` and arbitrary productions): the reads of a chunk from a phase and the carried phase compose over concatenation, and while `d` letters follow the chunk the run appends the productions of exactly those reads, through long queues with the expected heads; binary systems are the instance `0 → 0`, `1 → u` | `Jones1980.GTag.step`, `reads`, `nph`, `reads_append`, `nph_append`, `reads_row`, `run_chunk`, `TagSys.step_eq` | proved (`TagRead91.lean`) |
| **Undecidability of the encoded tag family, layer 2** (a 30-tag system simulating a single-register machine): register value as a count of `B` blocks among junk blocks before a marker block; multiplication rounds, division rounds by phase-shifting division sequences (`Q`/`C` blocks read back at the residue phase), the accepting round emitting the halting letter at a block start; the tag system reads `H` exactly when the machine accepts and never runs short before | `Jones1980.GTag.Seg`, `seg_chunk`, `GProg.tagP`, `cfg`, `round_mul`, `round_div`, `round_acc`, `gnext`, `reachesAcc_iff_gnext`, `tag_iff` | proved (`TagRound91.lean`) |
| **Undecidability of the encoded tag family, layer 3** (a binary system `0 → 0`, `1 → u` simulating a tag system with deletion `d`, after Neary's track-and-shift construction, STACS 2015, Lemma 9): `β = dL`, `u` of `s` rows whose tracks encode the productions; letters `0^{2(x+1)} u 0^{L−2(x+1)}` among garbage copies of `u`; a group of `d` letters is read in `β`-steps emitting the first letter's production; the halting letter's all-zero track flips the phase parity so that every later `u` emits zeros and the queue decays; with `s` even and `≡ 1 (mod β − 1)` and the initial length `≡ 1`, the binary system halts exactly when the tag system reads its halting letter, and the first-zero, positive-startup and single-zero-terminal promises hold | `Jones1980.DTag`, `DTag.rT`, `read_items`, `read_group`, `collapse`, `halts_AF`, `run_length_mod`, `sim`, `bin_iff` | proved (`TagBinary91.lean`) |
| **Universality of the 91-operation tag certificate** (the notes' citation of Neary's theorem, proved): for every recursively enumerable `S` there is a binary tag system with fixed constants `k, Ut, ε, B, cc` such that, with `C_x = 3^γ_x` above the admitted bound, `x ∈ S` exactly when `Sys91` is solvable at `(content W_x, 3^|W_x|)`; chain: Turing machine → three-counter program → single-register machine → 30-tag system → binary track system → `tag_iff91` | `Jones1980.CProgram.compile_wf`, `GProg.tagP_ok`, `tag_shape`, `dtag_ok`, `tagConst`, `tagConst_ok`, `CProgram.accepts_iff_halts`, `tag91_re` | proved (`TagUniversal91.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
| **Undecidability of the encoded tag family**: the instance map `x ↦ (γ_x, content W_x, 3^|W_x|)` is primitive recursive, and for the halting problem of partial recursive codes the solvability of `Sys91` over the family is not a computable predicate | `Jones1980.primrec_replicate`, `primrec_pow`, `primrec_content`, `DTag.primrec_W0`, `CProgram.primrec_instance`, `tag91_undecidable` | proved (`TagDecide91.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
| Radix geometry of the counter system: `R = 3^m` from `W = R³ ∣ q`, `m ∣ e` from the doubled head equation `H(R − 1) = 2(q − 1)`, hence `q = R^u` with `u ≥ 3` and `H = 2·heads m u` | `Jones1980.dvd_of_two_mul_pow_sub_one_dvd`, `heads_of_doubled_head_eq`, `geometry100` | proved (`Geometry100.lean`) |
| Pre-typing bounds of the counter system (§2): the fixed grid conditions of `ROM100.Ok`, including the port clause `8(hs + hz) < Zon`; the fixed-grid width `8 Zon + 9 ≤ R`, `R > K, g, 2gI, 32 S`, the doubled head equation, `16 S H < q`, `4 z H < q`, `4(A₀ + A₁) < q`, the packed-index sandwich, `C ≤ q`, the cyclic-route bounds `D < C`, `V < K C`, and `C < q` from `R ∣ q` | `Jones1980.ROM100.Ok`, `R_big`, `head_eq100`, `SH_small`, `zH_small`, `track_small`, `PC_le_q`, `D_lt_PC`, `PV_lt`, `PC_lt_q` | proved (`Bounds100.lean`) |
| **The twelve doubled fields** (§§3–5): once the six complements are nonnegative, every field is below `q`, so the Horner expansion of the packed word *is* its base-`q` chunk decomposition with no carry, and each field is twice a Boolean word below `rep e` | `Jones1980.Nonneg100`, `Jones1980.fields100` | proved (`Fields100.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
| Leading ternary trits: `Lead p t X`, uniqueness of the leading position and digit, the product rule, `2b` is `2`-led and `2v + 1` is `1`-led for Boolean `b, v`, and the even-field decoding step for doubled packed words | `Jones1980.Ternary.Lead`, `Lead.unique`, `Lead.mul`, `lead_two_of_bool`, `lead_one_of_odd`, `Lead.not_two_odd`, `chunk_step_even` | proved (`LeadingTrit.lean`) |
| The three borrow exclusions of §§3–4: the state residue is never odd, the route transfers the leading `2` of `KC` to `V` so the junk pair cannot borrow, the route parity forces `D` even; the halved state pair and its lowest row `2I`; the division of the cyclic route by the grid width; and the improved bounds `4 K S H < q`, `27 K² < q`, `2V < q`, `zH + (q−1)V < q²` | `Jones1980.state_residue_excludes_borrow`, `lead_of_route`, `D_even_of_route`, `bool_pair_first_row`, `state_first_row_le`, `state_first_row_eq`, `route_divided`, `ROM100.Sidon`, `junk_lead100`, `junk_no_borrow100`, `KSH_small`, `K_sq_small`, `PV_small`, `junk_carry_zero` | proved (`Borrow100.lean`), with the carry bookkeeping of §3 and the table's exponent layout as hypotheses |
| **The carry descent of §§3–4**: the packed word as the base-`q` Horner word of the twelve conceptual fields with genuine integer subtraction; the peel and the three ways to read a carry off bounds on the incoming value; the outgoing carry of a pair. The twelve levels then give: the sign pair exact, the zero pair at most one borrow and no outgoing carry, neither guard pair emitting a carry, `0 ≤ kappa ≤ K` for the junk pair, the state borrow excluded by the route residue, `C ≤ S H + kappa`, hence `2V < q`, hence `kappa = 0`, hence no junk borrow, hence `D` even and no zero borrow | `Jones1980.peel_abstract`, `peel_data`, `carry_zero`, `carry_borrow`, `carry_range`, `pair_carry_nonneg`, `pair_carry_le`, `pair_carry_zero`, `packed_horner100`, `nonneg_upper100`, `nonneg100` | proved (`Carry100.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
| **The guard complements** (§5): from the single quantitative consequence `2q ≤ R D` of the decoded controller (the reconstructed zero-request word is positive), the time equation and the head equation give `A₀ + A₁ < t`, so both guard complements are positive | `Jones1980.guard_poly`, `guard_key`, `guard_lt100` | proved (`Guard100.lean`) |
| **The decoding of the counter certificate**: all five nonnegativity statements, hence all twelve fields are twice a Boolean word below `rep e` | `Jones1980.nonneg_full100`, `Jones1980.decode100` | proved (`Guard100.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
| What the compiled program already gives: the marker exponent below the grid exponent, `2S` and `2I` below the state modulus, and — from the cyclic route read modulo that modulus — the residue `(7)` itself | `Jones1980.marker_lt_width`, `width_split`, `state_small`, `code_small`, `state_lt_width`, `route_residue100` | proved (`Compiled100.lean`) |
| **The counter certificate decoded from the compiled program**: every solution whose ROM has the Sidon layout, and which satisfies the table's exponent layout and the decoded-control bound `2q ≤ R D`, has all twelve conceptual fields equal to twice a Boolean ternary word below `rep e` | `Jones1980.decode_compiled100` | proved (`Compiled100.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
| The state-column layout: the state field's leading trit is a `2` at the minimum Sidon coordinate, since its lowest row is `2I = 2·3^amin`; hence the table's exponent layout `pK + aC < dm` | `Jones1980.ROM100.Layout`, `lead_state100`, `exponent_layout100` | proved (`Compiled100.lean`) |
| **The counter certificate decoded from the fixed program**: beyond the system and the compiled controller's Sidon and state-column layouts, the only remaining input is the decoded-control bound `2q ≤ R D` of §5 | `Jones1980.decode_layout100` | proved (`Compiled100.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
| The compiled fixed controller: at least two phase-split states with Sidon exponents `a i = 3^i`, and the fixed numerals `S`, `g`, `I`, `hs`, `hz`, `K` it compiles to. The coordinates are a Sidon set, so the edge exponents are distinct once the phase split has removed self-loops. The table is `1`-led at zero, because the last state's marker term contributes `3^(d−d) = 1` while every other exponent is positive; and the cyclic entry is state zero. So both layout hypotheses hold for every compiled controller | `Jones1980.Controller`, `Jones1980.sidon_coord`, `Controller.edge_exponent_inj`, `Controller.romK_mod`, `romK_lead`, `rom_sidon`, `rom_layout`, `Jones1980.decode_compiled_controller100` | proved (`Controller100.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
| **The fixed ROM and its projection** (routing note §1): the coordinates are a Sidon set; the edge exponents are distinct once the phase split has removed self-loops; the marker and port families are separated by their heights, so the table is a Boolean ternary numeral; and for a single selected state the digit of `K · 3^(a i)` at `d + a j` is `1` exactly when `j = f i`, while the marker term counts the step and the two port terms carry the labels | `Jones1980.Ternary.dg_sum_pow`, `Ternary.bool3_sum_pow`, `Jones1980.pow_add_pow_ne_pow`, `Controller.romK_eq`, `romK_bool`, `dg_romK_shift`, `dg_romK_shift_mark`, `dg_romK_shift_sgn`, `dg_romK_shift_zreq` | proved (`Controller100.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
| **The compiled ROM meets the fixed grid inequalities**, over a grid numeral built from the fixed program. The only one with content is `K < hz`: every table exponent is below `d + bz`, and a sum of distinct powers below a bound is below that bound's power. So the decoding's hypotheses are not vacuous, and `decode_controller100` needs nothing but the system and the decoded-control bound | `Jones1980.Controller.sum_pow_lt`, `expSet_subset`, `romK_lt_hz`, `zonChoice`, `rom_ok`, `Jones1980.decode_controller100` | proved (`Controller100.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
| The digitwise support test: when two Boolean words add to a third, each is digitwise below the sum, so a Boolean field whose complement is also Boolean vanishes wherever the sum does | `Jones1980.Ternary.dg_le_of_add`, `Ternary.dg_eq_zero_of_add` | proved (`Rows100.lean`) |
| **The rows of the state word** (§4, for every row): two Boolean words add without carries, so their quotients and remainders at any power add too; the fixed state word repeated once per row has quotient `S · heads m (u−i)` at the `i`-th row boundary; hence every row of the halved state word and of its complement add to `S`, so each row of the state word is a sub-word of the fixed state columns | `Jones1980.Ternary.add_mod_of_bool`, `Ternary.add_div_of_bool`, `Jones1980.heads_div`, `heads_row`, `state_row`, `state_row_le` | proved (`Rows100.lean`) |
| The fixed ROM fits inside a row: the zero-request port is below the grid width, and the marker and the table each fit inside a row when multiplied by the state word (the routing note's condition `W > K S`) | `Jones1980.hz_lt_R`, `KS_lt_R`, `gS_lt_R`, `Controller.pow_mem_le_romK`, `pow_coord_le_romS`, `Jones1980.rom_span_lt100`, `shift_span_lt100` | proved (`Bounds100.lean`, `Controller100.lean`) |
| **The row transport**: the product of the table with a one-hot history splits row by row, so the projection reads each row on its own. The digit of `K · C` at column `j` of row `i` is `2` exactly when `j` is the successor of the state selected in row `i`; the marker term counts the step and the two ports carry the labels | `Jones1980.Ternary.dg_two_mul`, `Ternary.dg_row`, `Jones1980.target_lt_width`, `row_fits`, `romK_mul_history`, `dg_target_row`, `dg_marker_row`, `dg_sgn_row`, `dg_zreq_row` | proved (`Transport100.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
| **The global-grid complement support**: if the on-grid word and the width coordinate are both Boolean and add to the grid word, the width coordinate vanishes wherever the on-grid word marks; so a junk field whose rows are sub-words of the width coordinate avoids every on-grid column. This is the disjointness the routing note gets from its `TestV` field and the counter note gets from its junk pair | `Jones1980.dg_complement_eq_zero`, `row_complement_grid`, `junk_avoids_grid` | proved (`Grid100.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
| **The fixed grid and its complement**: with spacing `B₀ = 3^ℓ` and row width `R = 3^(ℓ t)`, the width equation says the on-grid threshold and the width coordinate add to the grid word `heads ℓ t`, a `1` at every multiple of `ℓ` below the row width. With the threshold at a grid position, the width coordinate is that word with the one position deleted; it is Boolean, and its digits are known exactly | `Jones1980.heads_split`, `bool3_heads`, `grid_word`, `grid_complement`, `bool3_grid_complement`, `dg_grid_complement` | proved (`Grid100.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
| **The one-hot run** (routing note §5): from the route `K C = g·Next + V` and four support facts — the rows of the state word are sub-words of the fixed state word, the junk avoids the target columns, the rows of the next-state word are sub-words of the fixed state word, and the next-state word's rows are the state word's later rows — every row of the state word selects a single state, and the state of row `i` is the `i`-th iterate of the successor from the entry state. This is the fixed ROM and count-marker argument that §5 of the counter note hands to the published 101/102 predecessors | `Jones1980.Ternary.eq_of_dg_eq`, `Controller.dg_romS`, `onehot_of_dg`, `row_romK_mul`, `onehot_step`, `iterate_lt`, `onehot_run` | proved (`OneHot100.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
| **The grid layout and the junk side of the route**: the grid layout `ROM100.Grid` says the spacing is a power of three, the on-grid word is Boolean and it marks every target column. With it, the junk field avoids the target columns and the two port terms sit above them, so the whole junk side of the route contributes nothing there and the transport reads the target columns against the shifted state word alone | `Jones1980.ROM100.Grid`, `Jones1980.row_mul`, `dg_port_row`, `route_junk_vanishes` | proved (`OneHot100.lean`, `Grid100.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
| **The support facts from the counter system**: the carry descent now also exports the halved state pair (`PC = 2 pc` with `pc`, `pcbar` Boolean and `pc + pcbar = S · heads m u`), each row of which is digitwise below the fixed state word; and the next-state word `C/R + 2I·(q/R)` has, below its top row, exactly the later rows of the state word | `Jones1980.state_halves100`, `state_row_support`, `row_div_pow`, `row_add_mul_pow`, `row_next` | proved (`Carry100.lean`, `Rows100.lean`, `Route100.lean`) |
| **The decoded controller** (§5): eight of the twelve fields are halved straight from the carry descent, without reading the guard pairs; the halves supply the state support, the global-grid complement support (the width coordinate is Boolean because the on-grid word marks only grid positions below the row width) and the two label supports; the junk word is Boolean because the ports are on-grid; and the fixed ROM and count-marker argument is the one-hot run. So every positive solution of `Sys100` over a compiled controller's ROM with the grid layout has a state field `C = 2c` whose row `i` is the single state `f^[i] 0`; the last state's successor is the cyclic entry; and the zero field's last row carries the last state's zero-request label | `Jones1980.Ternary.bool3_sub_of_dg_le`, `row_eq_zero_of_ge`, `mul_lt_of_rows`, `grid_complement_bool`, `decoded_path100` | proved (`Decode100.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
| **The decoded-control bound is a theorem** (§5): under the compiler's terminal convention that every predecessor of the cyclic entry carries the no-zero-request label, the zero field's top row is set, so `2q ≤ R D`. Hence the controller returns to its entry after `u` steps, and all twelve fields decode with no decoded-control hypothesis | `Jones1980.decode_bound100`, `decoded_controller100`, `decode_all100` | proved (`Decode100.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
| **A compiled on-grid word**: with spacing `B₀ = 9` and odd port offsets, the numeral marking every target column, both port columns and one high column meets both `ROM100.Ok` and `ROM100.Grid`. So for a compiled controller with odd port offsets and the terminal convention, every positive solution of `Sys100` over its own ROM has the radix geometry, satisfies the decoded-control bound, returns to the cyclic entry, and has the controller path as its state field, with no assumption about the fixed ROM left | `Jones1980.Controller.gridSet`, `gridZon`, `rom_grid_ok`, `rom_grid_layout`, `Jones1980.decoded_compiled100` | proved (`GridCompiled100.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
| **The counter history** (raw-counter note §§2–3, counter note §5): halving the track, sign and zero fields, every block of the halved track word is at most `(R − 3)/3` and vanishes wherever the zero field's row is empty (the source-zero test); each sign row is `±1`; the three residue chains start at `[2x, 0, 0]`; and each block equals the block three places earlier plus that block's sign, up to three places past the top, so the chains end at zero. The engine is that a signed base-`R` numeral with digits smaller than `R` vanishes only digitwise | `Jones1980.signed_digits_zero`, `row_add_small`, `row_add_of_bool`, `six_dvd_pow_sub_three`, `sum_rows_int`, `counter_history_rom100` (any ROM with the Sidon and state-column layouts and the decoded-control bound), `counter_history100` (its deterministic-controller corollary) | proved (`Counters100.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
| **Scope of the controller results above**: `Controller` has a single successor function, so everything from `Controller100.lean` through `GridCompiled100.lean` is the *deterministic* router (`EXPLORATION_FIXED_PROGRAM_ROUTING.md` §5), where the junk may be excluded from the target columns (`ROM100.Grid.marks_targets`). The compiled universal machine needs branching (`EXPLORATION_THREE_RAW_COUNTER_UNIVERSAL_COMPILER.md` §4), and the counter note's ROM is the *nondeterministic* router of `EXPLORATION_NONDETERMINISTIC_PROGRAM_ROUTING.md`: the table carries every permitted edge, unchosen edges stay in the junk at target columns, and a column-count marker forces one state per row. A deterministic controller cannot branch on a zero test, so these results do not reach universality | — | recorded; the counter history (`Counters100.lean`) does not depend on determinism |
| **The graph router's table** (nondeterministic routing note §§1–2): a graph controller has states `i < n`, Sidon coordinates `3^i`, an irreflexive edge relation, and grid spacing `sp` with `n < 3^sp`. Its table carries one term per permitted edge at block `bmark + a j − a i`, a marker term per state at block `bmark − a i`, and the two label ports; all block exponents are distinct, so the table is a Boolean ternary numeral whose digits are known exactly | `Jones1980.Graph`, `Graph.edgeE_inj`, `markE_inj`, `sgnE_inj`, `zreqE_inj`, `edgeE_ne_markE`, `bexpSet`, `romK`, `dg_romK`, `romK_bool` | proved (`Graph100.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
| **The count marker** (routing note §1): a Boolean word digitwise below the fixed state word selects a set `U` of states, and the marker block of `K · c_U` is exactly `|U|`; for a single state the target digit at `d + a j` is the edge bit and the port digits are the labels | `Graph.romS`, `dg_romS`, `selWord`, `eq_selWord`, `count_marker`, `dg_single_target`, `dg_single_marker`, `dg_single_sgn`, `dg_single_zreq` | proved (`GraphCount100.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
| The graph router's ROM: the numerals `g`, `I`, `hs`, `hz`, `S`, `K` over the spacing grid, with the Sidon and state-column layouts; and `Graph.PortGrid`, which asks only that the on-grid word be Boolean, lie on the spacing grid and mark both port columns — unlike the deterministic grid layout it lets the junk occupy target columns | `Graph.romg`, `romhs`, `romhz`, `romI`, `rom`, `romK_lead`, `rom_sidon`, `rom_layout`, `Jones1980.Graph.PortGrid` | proved (`GraphRom100.lean`) |
| **The path recovery** (routing note §5): from the route `K C = g·Next + V`, Boolean fields, the row supports, the shift of the next-state word and a fixed singleton top row, with the junk vanishing only inside the marker block: the marker block of each row counts its states against a Boolean digit, so each row has at most one state; an empty row empties every later row, contradicting the top; and for consecutive singletons the target digit forces a permitted edge | `Jones1980.block_eq_digit`, `Graph.dg_selWord_lt`, `Graph.path_run` | proved (`GraphRun100.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
| **The decoded nondeterministic path** (counter note §5, over the counter note's own ROM): every positive solution of `Sys100` over a graph controller's ROM with the port-grid layout halves its state, sign and zero fields and has a state sequence starting at the entry whose `j`-th state is row `j` of the state word, whose consecutive states are permitted edges, whose last state has an edge back to the entry, and whose labels are rows `j` of the sign and zero fields. The junk may occupy target columns; the path recovery needs it to vanish only off the spacing grid, where the width coordinate is zero. Under the terminal convention (every predecessor of the entry has no zero request), `2q ≤ R D` | `Jones1980.graph_path100`, `graph_decode_bound100` | proved (`GraphDecode100.lean`) |
| **A compiled graph ROM**: for every graph controller, with spacing `B₀ = 3^sp`, the table's block exponents are all below `bmark + bz` so `K < hz`, and the numeral marking both port columns and one high column `sp · zonChoice` meets both `ROM100.Ok` and `Graph.PortGrid`. So under the terminal convention every positive solution of `Sys100` over a graph controller's own ROM has the radix geometry, the decoded-control bound, and a state field tracing a path of permitted edges from the entry back to it, with the sign and zero fields carrying the labels | `Graph.romK_lt_hz`, `Graph.zonChoice`, `gridSet`, `gridZon`, `rom_grid_ok`, `rom_port_grid`, `Jones1980.graph_decoded_compiled100` | proved (`GraphCompiled100.lean`) |
| **Every positive solution is an accepting serial run** (serial composition note §§1, 6): `Graph.SerialRun` is the serial labelled-counter relation — states from the entry along permitted edges with an edge back to the entry; block values starting at `[2x, 0, 0]`, each moving by its source state's sign three blocks later, zero wherever the source state requests a zero test (`zreq = false`), and all three registers ending at zero. Under the terminal convention, every positive solution of `Sys100` over a graph controller's own compiled ROM has the radix geometry and is such a run on input `x` | `Jones1980.Graph.SerialRun`, `graph_serial_run100` | proved (`GraphHistory100.lean`) |
| **Compiling a three-counter program** (universal compiler note §§4–6): logical programs with increments, zero-or-decrement tests with two successors, an accepting halt and a dead stop; acceptance means reaching the halt from `(x, 0, 0)` with all registers zero. The compiled graph doubles every logical value and spends two banks of three lanes per instruction (increment; zero branch with a zero request; nonzero branch decrementing first; halt with three zero requests), after a `+1`/`−1` prefix; the halt's last lane leads back to the entry, the only edge into it | `Jones1980.CInstr`, `CProgram`, `CProgram.Step`, `Accepts`, `graph`, `adj_true`, `entry_true`, `bankNext_slot`, `sgnSL_slot`, `zeroSL_slot`, `bankNext_to_zero` | proved (`CounterProgram100.lean`) |
| **Serial runs of a compiled program are accepting computations** (§§5–6): the run sits at lane `b mod 3`, cannot stop before the halt's last lane, and every six blocks passes one logical step with physical values twice the logical ones; the zero branch needs a zero register, the nonzero branch a positive one, and the halt all zeros. So a positive solution of `Sys100` over the compiled ROM of a program implies the program accepts `x` | `CProgram.run_lane`, `run_cont`, `run_bank`, `run_bank_val`, `run_zero`, `run_exit`, `accepts_of_run`, `Jones1980.accepts_of_sys100` | proved (`CounterSound100.lean`) |
| **Accepting computations are serial runs of the compiled program** (§5, completeness): an accepting computation of `K` steps is laid out as `6 + 6(K + 1)` blocks — the prefix, then two banks per configuration, entering a test at its zero branch exactly when the register is zero — with physical values twice the logical ones at the first bank and moved by its signs at the second; every field of `Graph.SerialRun` holds. So a program accepts `x` exactly when its compiled graph has an accepting serial run on `x` | `CProgram.exists_seq`, `kindOf`, `slotAt`, `runSt`, `runVal`, `step_cases`, `zeroSL_bank`, `sig_slot`, `run_of_seq`, `run_of_accepts` | proved (`CounterComplete100.lean`) |
| **The positive converse assembly** (counter note §6): the halves of the twelve fields (`k⁺, k⁻, h − d, d, t/2 − a₀, a₀, t/2 − a₁, a₁, zh − v, v, Sh − c, c`) Boolean and below `q = 3^e`, the first with unit digit `1`, `h` even, and the outer equations in halved form give a positive solution of `Sys100`: the packed index `r = P/2 + rep(12e)` has the unit-two mask, lies in `(q¹²/2, q¹²)`, is even, and the positive kernel converse supplies the Pell witnesses | `Jones1980.assemble100` | proved (`Assemble100.lean`) |
| **The canonical witness of a run** (serial composition note §7, counter note §6): for a single step, the table product of the state minus its target and labelled ports is a Boolean junk row on the spacing grid, off both ports, below the high grid column, with the marker digit kept; a counter value splits into two Boolean words, both positive on the even input block; and a run satisfies the factored time equation `R³(A + κ⁺) + 2x = A + R³κ⁻` | `Graph.chosen`, `junkRow`, `chosen_le`, `bool3_junkRow`, `junkRow_support`, `dg_junkRow_marker`, `Jones1980.Ternary.le_of_dg_le`, `dg_sub_of_dg_le`, `splitLo`, `splitHi`, `splitHi_add_splitLo`, `splitLo_pos`, `splitHi_pos`, `Graph.time_equation` | proved (`WitnessRoute100.lean`, `WitnessSplit100.lean`) |
| **Every accepting serial run gives a positive solution** (§7 / §6): with radix `R = 3^m`, `m = sp·T` for `T` past the high grid column, the input, the values and `K S`, the rows of the twelve halved fields are the states, labels, split values, `rep(m − 1)` on no-zero-request rows and the junk rows, the width coordinate is `heads(sp, T) − Zon`, and `assemble100` finishes — when the first sign is plus, the terminal convention holds and the run has even length | `Jones1980.solvable_of_run` | proved (`WitnessRun100.lean`) |
| **Acceptance by a three-counter program is 100-operation Diophantine** (counter note §6, "both directions"): for every program `M` and `x > 0`, `M` accepts `x` iff `Sys100` over the compiled ROM of `M` has a positive solution at `x` | `Jones1980.CProgram.graph_conv`, `graph_sgn0`, `run_of_accepts`, `Jones1980.accepts_iff_solvable100` | proved (`CounterIff100.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
| **Counter-program macros** (universal compiler note §1): the step relation as a deterministic partial function; placed instruction blocks; transfer (`s += r`), multiplying transfer (`s += k r`), increment chains, push (`r := k r + d` with a zero scratch) and pop (`r := r / k`, exiting by the remainder, restoring the scratch), each with its reachability specification | `CProgram.next`, `step_iff_next`, `Placed`, `transferM`, `transfer_spec`, `incsM`, `incs_spec`, `mulTransferM`, `mulTransfer_spec`, `pushM`, `push_spec`, `popM`, `pop_spec` | proved (`CounterMacros100.lean`) |
| **A three-counter program simulating a Turing machine** (universal compiler note §§2–3): tape halves are stack numbers in base `|Γ| + 2` with nonzero digits (blank has a positive code, an empty stack pops blank); the loader moves the binary digits of `x` onto `B`, most significant on top; each step pops the scanned symbol from `B` and writes, moves right or moves left by pushes and pops; a halt clears the registers and accepts. For every Mathlib `TM0` machine with finite symbol and state types and every encoding of bits, the program accepts `x` iff the machine halts on the binary digits of `x`, most significant first | `Jones1980.TMStack.stk`, `Good`, `head_stk`, `tail_stk`, `cons_stk`, `lsbBits`, `loadB`, `loadB_spec`, `Jones1980.TMCounter.prog`, `placed`, `load_spec`, `loop_spec`, `clean_spec`, `Dsp`, `step_sim`, `halt_sim`, `respects`, `accepts_iff` | proved (`TuringStack100.lean`, `TuringCounter100.lean`, `TuringSim100.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
| **Recursively enumerable sets are halting sets of finite machines on binary input** (compiler note, opening), from Mathlib's verified compilers with no new axiom: a `ToPartrec.Code` for the semidecision (`Code.exists_code`), `PartrecToTM2` started at that code, `TM2to1`, `TM1to0`, and the restriction of the resulting `TM0` machine to its finitely many supported states; the input tape is one marker cell followed by the binary digits, most significant first. The simulating program takes that fixed prefix | `Jones1980.TMUniv.finite_machine`, `trNat_eq`, `trInit_trList`, `re_tm0`, `Jones1980.TMCounter.pushList`, `pre_spec`, `accepts_iff` | proved (`TuringPartrec100.lean`, `TuringSim100.lean`) |
| **Universality of the 100-operation system**: for every recursively enumerable `S` there is a fixed ROM `C` with `x ∈ S ↔ Solvable100 C x` for every `x > 0` | `Jones1980.universal100_re` | proved (`Universal100.lean`); axioms `propext`, `Classical.choice`, `Quot.sound` |
What carries over unchanged to later versions: the relaxed auxiliary
norm, the ratio and exponent decodings, the three-mask packing, the
window arithmetic, the canonical-code identification, and the compiler;
what must be redone per version: the transcription, the bootstrap
bounds, the signed-index step, and the index construction and decoding.

## Article defects found while formalizing

None so far.  Points recorded for the editorial notes: the equations of
Corollary 2.6 and Theorem 2.12 must be read as integer equations (the
article says so implicitly); with truncated subtraction (III) of Corollary 2.6
would admit spurious solutions such as `a = 2, n = 1, y = 4, r = 0`.

The 1982 Theorem 1 checks are recorded in `Papers/EDITORIAL_NOTES.md`:
the binomial upper arguments are nonnegative consequences of the equations,
and the odd-product witness `η` is strictly positive. The apparent sign issue
in the §4 estimate for `S₃` is not an error: the preceding paragraph establishes
`0 < D₀`. No article-source correction was needed for this milestone.

## Validation — 2026-09-14, Theorem 1 checkpoint

- Full `lake build` succeeded (3073 Lake jobs, including dependencies).
  The root module imports all 56 project source modules, including `Index`
  and `Theorem1`. Existing deprecation and linter warnings remain.
- `#print axioms` for `Jones1982.exists_index_above`, `exists_index`,
  `UEqs.S3_nonneg`, `master`, `theorem_1`, and `theorem_1_representation`
  reported exactly `[propext, Classical.choice, Quot.sound]` for each.
  No project mathematical axiom or `sorryAx` appears in these dependencies.
- A source scan of `Diophantine/` and `Diophantine.lean` found no `sorry`,
  `admit`, or `axiom` tokens. `git diff --check` passed.
- No article TeX or PDF changed in this milestone; no PDF rebuild is claimed.

## Validation — 2026-09-14, Theorem 2 and Pell lemmas checkpoint

- Six new modules passed serialized focused compilation. One consolidated
  `lake build` then succeeded (3079 Lake jobs, including dependencies), with
  all 62 project source modules imported by the root. Existing deprecation
  and linter warnings remain; the new modules passed without new warnings.
- `#print axioms` checked `pack3_carries_iff_dvd`,
  `centralCode_eq_rPolynomial`, `UEqs.packing_bounds`, `UEqs.packing_sizes`,
  `theorem_2`, `lemma_2_26`, `lemma_2_26'`, `lemma_2_27`,
  `ProductPellConds.coprime_J`, and `exists_positive_pell_quotient_int`, all
  in `Jones1982`. Their dependencies are subsets of
  `[propext, Classical.choice, Quot.sound]`. No project mathematical axiom
  or `sorryAx` appears; the polynomial identity does not require choice.
- The project Lean source scan again found no `sorry`, `admit`, or `axiom`
  tokens. The root import inventory covers every project module, and
  `git diff --check` passed.
- Editorial notes record the checked bounds, positivity arguments, and
  exact integer interpretations. No article TeX or PDF changed, and no
  PDF rebuild is claimed. Theorem 3 and the §5 universality proof remain
  unfinished parts of the continuing formalization.

## Validation — 2026-09-14, Theorem 3 checkpoint

- The six new modules passed serialized focused compilation. One consolidated
  `lake build` then succeeded (3085 Lake jobs, including dependencies), with
  all 68 project source modules imported by the root. Existing deprecation
  and linter warnings remain; none of the new modules has a warning in the
  consolidated build.
- `#print axioms` checked `UEqs.b_gt_mul`, `exists_ratioPolynomial`,
  `RatioPolynomial.sound`, `theorem_3`, `theorem_3_representation`,
  `pow_add_mul_psi_lt_chi`, and `exists_positive_pell_power_quotient_int`,
  all in `Jones1982`. Every result reports exactly
  `[propext, Classical.choice, Quot.sound]`. No project mathematical axiom
  or `sorryAx` occurs in these dependencies.
- The Lean source scan found no `sorry`, `admit`, or `axiom` tokens. The
  root import inventory covers all project modules, and `git diff --check`
  passed. Independent statement review checked the eighteen equations,
  twenty-eight positive witnesses, signed subtractions, and absence of a
  circular power-of-two assumption in the converse.
- Editorial notes retain these proof details and the positive quotient
  needed for §5 (D3). No new article error was found in the checked passages.
  No article TeX or PDF changed, and no PDF rebuild is claimed.

## Validation — 2026-09-14, shorter coding and packing checkpoint

- The twelve new modules passed focused compilation. The consolidated
  `lake build` succeeded (3097 Lake jobs, including dependencies), with
  all 80 project source modules imported by the root. After the final
  review corrected the explanatory comment in `Psi.lean`, that module
  and the consolidated build passed again. Existing deprecation and
  linter warnings remain; the twelve new modules have no warnings.
- `#print axioms` checked `coeff_shortHpoly_Lexp`,
  `abs_coeff_shortHpoly_le`, `natDegree_shortHpoly_lt`, `short_tau3_iff`,
  `exists_short_D8_cutoff`, `exists_shortEqs_of_digits`, `short_code_iff`,
  `ShortEqs.transfer_iff`, `short_packing_bounds`, `short_packing_iff`,
  `short_packing_sizes`, `short_master`, and `short_master_packed`, all
  in `Jones1982`. Each of the thirteen results reports exactly
  `[propext, Classical.choice, Quot.sound]`; no project mathematical
  axiom or `sorryAx` appears in their dependencies.
- The source scan found no `sorry`, `admit`, or `axiom` tokens. The root
  import inventory covers all 80 project modules. Independent review
  checked the twelve positive witnesses, normalization, signed masks,
  packing formulas, and absence of circular size assumptions.
- Editorial notes preserve the degree and coefficient bounds, the
  eventual-positivity argument for (D8), the top-digit transfer of `e`,
  and the proof-note correction for the harmless Pell boundary case.
  No article equation error was found in the checked passages. No article
  TeX or PDF changed, and no PDF rebuild is claimed. These are local build
  and proof-audit receipts; no remote CI run is claimed.

## Validation — 2026-09-14, full §5 system and explicit quartic checkpoint

- All eight new modules passed serialized focused compilation. One
  consolidated `lake build` then succeeded (3105 Lake jobs, including
  dependencies), with all 88 project source modules imported by the root.
  Existing deprecation and linter warnings remain; none of these eight
  new modules has a warning in the consolidated build.
- `#print axioms` checked seventeen results: `exists_shortPell`,
  `ShortPellWitnesses.sound`, `ShortPolynomialWitnesses.packing_eqs`,
  `ShortPolynomialWitnesses.sizes`, `mem_of_shortPolynomial`,
  `exists_shortPolynomial_of_packed`, `short_polynomial_master`,
  `short_polynomial_representation`, `short_ratio_iff`,
  `ShortQuadraticVar.card`, `ShortQuadraticEquation.card`,
  `ShortQuadratic.residual_totalDegree_le_two`,
  `ShortQuadratic.sumSquares_totalDegree_le_four`,
  `ShortQuadratic.eval_sumSquares_eq_zero_iff`,
  `ShortQuadratic.shiftedSumSquares_totalDegree_le_four`,
  `Index.two_mul_lt_u`, and `ShortQuadratic.index_normalized`, all in
  `Jones1982`. The packing identities use only `propext`; the other
  sixteen results report `[propext, Classical.choice, Quot.sound]`.
  No project mathematical axiom or `sorryAx` occurs in these dependencies.
- The source scan found no `sorry`, `admit`, or `axiom` tokens. The
  witness-field inventory found 26 outer scalars and 27 Pell scalars,
  giving the 53 explicit quantities. Lean proves the separate finite
  cardinalities of 58 quadratic witnesses and 46 residual equations.
  Independent review checked all equation groups, positivity, signed
  quantities, degree-certificate interpretation, and normalization.
- The editorial notes retain the converse's noncircular order, both
  positive Pell quotients, the exact rational (D21) interpretation, and
  the degree-reduction and normalization details. No new article equation
  error was found. No article TeX or PDF changed, and no PDF rebuild is
  claimed. These are local build and proof-audit receipts; no remote CI
  run is claimed. Solvability preservation from 53 to 58 witnesses and
  recursively enumerable universality remain unproved by this checkpoint.

## Validation — 2026-09-14, normalized 58-witness quartics for Diophantine sets

- All eight new modules passed serialized focused compilation. After
  merging `origin/main` at `9ae5373c9fc54842c265cbf2e3d53199d9090f1c`,
  one consolidated `lake build` passed (3113 Lake jobs, including
  dependencies). The root imports all 96 project source modules. Existing
  deprecation and linter warnings remain; none of the eight new modules
  has a warning in the consolidated build.
- `#print axioms` checked fourteen results:
  `ShortPolynomialWitnesses.exists_positiveWitnesses`,
  `ShortQuadratic.PositiveWitnesses.exists_shortPolynomial`,
  `short_polynomial_iff_quadratic`,
  `ShortQuadratic.quartic58_totalDegree_le_four`,
  `ShortQuadratic.wset_quartic58_iff`,
  `ShortQuadratic.quartic58_index_normalized`, `short_quartic_master`,
  `short_quartic_representation`,
  `EnumerationQuadratic.mem_W_iff_gateSys`,
  `EnumerationQuartic.residual_totalDegree_le_two`,
  `EnumerationQuartic.wset_quartic_iff`,
  `EnumerationQuartic.quartic_normalized`,
  `EnumerationQuartic.exists_normalized_quartic_representation`, and
  `diophantine_quartic58`, all in `Jones1982`. Every result reports exactly
  `[propext, Classical.choice, Quot.sound]`; no project mathematical axiom
  or `sorryAx` occurs in these dependencies.
- The source scan found no `sorry`, `admit`, or `axiom` tokens. The import
  inventory covers all 96 project modules without missing sources or
  imports. Independent review checked all 46 residuals, the positive
  witness constructions, the signed-to-natural conversions, both coordinate
  renamings, the fixed coding parameters, and the positive-input scope.
- The requested upstream merge preserved every in-progress Lean file
  byte-for-byte and both sets of documentation edits; there were no merge
  conflicts. The merged 1980 operation-count work is separate from this
  Lean receipt. This formalization batch changes no article TeX or PDF,
  and claims no PDF rebuild or remote CI run. No new article error was
  found in the checked equations. Editorial notes retain the substitution,
  positivity, finite-gate, and normalization arguments.

## Validation — 2026-09-14, Mathlib representations and pairing

- All five new modules passed serialized focused compilation:
  `MathlibPolynomial`, `MathlibDiophFinite`, `MathlibDiophBridge`,
  `MathlibQuartic`, and `DiophantinePairing`. After merging upstream
  `5f36d2bc2941ce79c8df2e9f2183edfb44ac7e64`, one consolidated `lake build`
  passed (3122 Lake jobs, including dependencies). The root imports all
  101 project source modules. The five new modules have no warnings in
  the consolidated log; existing warnings elsewhere remain.
- `#print axioms` checked all fourteen new public theorems:
  `Diophantine.isPoly_eval_mvPolynomial`,
  `Diophantine.isPoly_iff_exists_mvPolynomial`,
  `Diophantine.exists_fin_witness_polynomial`,
  `Diophantine.dioph_iff_exists_fin_polynomial`,
  `Jones1978.isDiophantine_iff_mathlib_dioph`,
  `Jones1978.IsDiophantine.mathlib_dioph`,
  `Jones1978.IsDiophantine.inter`, `Jones1978.IsDiophantine.union`,
  `Jones1978.isDiophantine_powers`,
  `Jones1982.mathlib_dioph_quartic58`, `Jones1982.powers_quartic58`,
  `Diophantine.pair_dioph`, `Diophantine.unpair_left_dioph`, and
  `Diophantine.unpair_right_dioph`. Two further checks cover the imported
  `Dioph.pow_dioph` and `Jones1978.S_eq_P`. Every one of these sixteen
  results reports exactly `[propext, Classical.choice, Quot.sound]`.
  No project mathematical axiom or `sorryAx` occurs in their dependencies.
- The proof-source scan found no `sorry`, `admit`, `axiom`, or
  `native_decide` tokens. The import inventory covers all 101 modules.
  Independent review checked finite support, preservation of input
  coordinates, empty witness types, both coordinate renamings, power bases
  zero and one, pairing branches, and inverse-pairing witnesses.
- The adapter's set equivalence covers every natural input, including zero.
  The quartic corollaries retain the positive-input restriction and choose
  one normalized polynomial uniformly for those inputs. The pairing
  primitives do not require positive values or finite input index types.
- Corrected the `S_eq_P` proof comment from `3n+1` to the theorem's actual
  `3n−1` bound and retained the explanation in the editorial notes. The
  documented axiom policy now includes the project owner's allowance for
  obvious elementary facts; this batch adds no mathematical axiom.
- The upstream merge preserved the seven in-progress proof/source files
  byte-for-byte and restored the editorial patch unchanged. The merged
  1980 operation-count work is separate from this Lean validation. This
  batch changes no article TeX or PDF and claims no PDF rebuild or remote
  CI run. `TRACE_INTEGRATION.md` records source-inspected external
  candidates; none has been integrated or kernel-audited here yet.

## Validation — 2026-09-14, recursively enumerable universality

- All twelve vendored proof modules, their standalone umbrella, and the six
  new project modules passed serialized focused compilation. One consolidated
  `lake build` passed with 3150 Lake jobs, including dependencies. The project
  umbrella imports all 107 project modules plus `PAListCoding`. None of the
  six new project modules has a warning in that consolidated build; existing
  deprecation and linter warnings elsewhere remain.
- `lake env lean Computability/HilbertTenthProblem/Lean/checks/RecursivelyEnumerableAxioms.lean` passed all thirty
  `#print axioms` checks. The audit covers all nineteen new public theorems,
  ten vendor closure/trace results, and `Nat.Partrec.Code.primrec_evaln`.
  Every result reports exactly `[propext, Classical.choice, Quot.sound]`.
  In particular, `Diophantine.rePred_dioph`, the three printed-system
  corollaries, specialization equality, and `Jones1982.universal_quartic58`
  have no project mathematical axiom or `sorryAx` dependency. The complete
  declaration list is retained in the reproducible
  [audit source](checks/RecursivelyEnumerableAxioms.lean).
- The source inventory covers all 107 project modules and all twelve vendor
  proof modules, each imported exactly once by its umbrella. A nested-comment
  and string-aware scan of the 121 library source files, including both
  umbrellas, found no code tokens `sorry`, `admit`, `axiom`, or `native_decide`.
  All fourteen vendored SHA-256 entries and all thirteen original source
  hashes match their recorded values. The 99-line trace extraction and
  single import replacement were checked exactly. All 27 local vendor
  import edges resolve; its external imports are Mathlib modules only.
- Independent review checked zero-length primitive recursion, arbitrary
  Diophantine input substitutions, the fixed program code and encoding of
  bounded evaluation, all witness counts, and the distinction between the
  §4 exponent `5^60` and the fixed §5 exponent `L4 58 = 5^59`. The universal
  statement chooses one joint polynomial before the represented set. Its
  degree bound applies after specializing the three index parameters and
  counts the input and 58 natural witnesses. The RE-to-Diophantine bridge
  includes zero; the article representations retain positive-input scope.
- The upstream merges through `e07104048eb69f75caf19b9a543937a81c742c04`
  preserved all 123 checked files (the library sources, audit source, and
  Lake configuration) byte-for-byte, and merged the documentation
  cleanly. There are no merge conflicts. Incoming 1974/1976 edition changes
  and the 1980 operation-count work are separate from this Lean receipt.
  This formalization batch changes no article TeX or PDF and claims no PDF
  rebuild or remote CI run. The editorial notes retain the computability,
  fixed-polynomial, degree, and domain clarifications; no additional article
  equation error was found in this batch.

## Validation — 2026-09-14, 1980 announcement checkpoint

- New modules `Paper1980/IndexCode.lean` and `Paper1980/Theorem5.lean`
  compiled, and the root module (with the two new imports) built with
  `lake build` before the merge with the concurrent relation-combining
  milestone (8778 jobs) and again after it (8790 jobs, exit 0).
- `#print axioms` for `Jones1980.indexCode_injective` and
  `Jones1980.theorem_5` reported exactly
  `[propext, Classical.choice, Quot.sound]` (`.lake/paper1980-axioms.log`).
  No project axiom was introduced although the policy for this article
  allows well-known pre-1980 theorems and obvious facts as axioms.
- No statement of the 1980 announcement that also appears in the 1982
  article was restated; the docstrings of `Jones1982.Thm1`, `Thm2`,
  `theorem_1`, `theorem_2`, `theorem_3` and `universal_quartic58` now
  record the double appearance.
- Environment note: two full builds in this worktree failed only with
  `failed to read file … .olean` errors at import time (line 1:0) on
  Mathlib oleans reached through the `.lake/packages` junction, on
  different modules each time and with the files intact and unchanged;
  a rerun succeeded. `lake -j` is not accepted by this Lake version as a
  build option.

## Next article frontiers

The computability bridge and the universal pair `(58,4)` are proved.
The proof uses Mathlib's `REPred` and bounded evaluator together with
verified primitive-recursion and finite-trace representations. The vendor
sources, extraction boundary, and mathematical interfaces are documented in
[TRACE_INTEGRATION.md](TRACE_INTEGRATION.md). Double compression fixes the
family exponent before the represented set is chosen, and specialization
equality packages the result as one ordinary joint polynomial. The article's
degree convention excludes the three fixed index parameters; representation
is explicitly restricted to positive inputs.

This closes the previously missing r.e. input to Theorems 1–3 and the
58-witness quartic. It does not complete all six article formalizations.
The relation-combining theorem and original twelve-variable prime-polynomial
existence are proved. The refined source now includes individual weights,
the five-square replacement, degree bounds, and an exact-degree-13697
construction using positive padding. Theorem 3's exact zero-test range
with eleven auxiliary variables is also proved. The consolidated build
and transitive axiom audits pass, as recorded below. Equality for the unpadded five-square polynomial is not
asserted. Remaining article work includes the 1982 nine-unknown construction
and later variable/degree tradeoffs, together with unfinished statements in
the tables. The construction and degree distinctions are recorded in
[RELATION_COMBINING_FRONTIER.md](RELATION_COMBINING_FRONTIER.md).
Two bounded next steps in the 1976 article are now identified. Theorem 4
can use the primitive-recursive graph
`Nat.Prime m ∧ Nat.count Nat.Prime m = n-1`, the proved Diophantine
bridge, finite polynomial extraction, and Putnam's positive-value device.
That route supplies finitely many witnesses; the additional fourteen-witness
refinement needs its own reduction. Theorem 5 can connect the existing
[87-operation schedule](../Papers/verification/jones1976_primality87.md) to
`Thm212System` through typed references to earlier integer temporaries.
Its ten subtraction assignments must be checked as additions, giving
40 additions and 47 multiplications; comparison and domain checks are
outside that arithmetic count. These are implementation plans, not
formalized results.

In particular, the 1984 result `JM1984.RM.accepts_iff` characterizes
a supplied well-formed register program by its encoding system. A compiler
from arbitrary computability data into that specific register-machine
model remains a separate article-specific obligation; the bounded-evaluator
proof of DPRM does not provide that compiler.

## Validation — 2026-09-14, relation combining and twelve-variable primes

- One consolidated `lake build` passed after the focused dependency checks,
  with 3555 Lake jobs including dependencies. The umbrella imports all
  119 project modules, plus the twelve vendored proof modules through their
  umbrella. The twelve new project modules have no warnings in the
  consolidated log; existing deprecation and linter warnings elsewhere
  remain. The final twelve-variable application and project umbrella were
  compiled in this consolidated build.
- `lake env lean Computability/HilbertTenthProblem/Lean/checks/RelationCombiningAxioms.lean` passed all 37
  transitive axiom checks. Every result reports exactly
  `[propext, Classical.choice, Quot.sound]`. The reproducible
  [audit source](checks/RelationCombiningAxioms.lean) includes the norm
  estimates, Galois fixed-field interface, sign-invariance construction,
  polynomial substitution, both arithmetic directions, denominator
  equivalence, elimination, and the final prime-polynomial theorems.
  No project mathematical axiom or `sorryAx` occurs in these dependencies.
- A nested-comment and string-aware scan of all 133 library Lean files,
  including both umbrellas, found no code tokens `sorry`, `admit`, `axiom`,
  or `native_decide`. The import inventory includes every project source
  exactly once. All twelve new modules were independently checked against
  the consolidated warning log. A 137-file source/configuration hash
  receipt records the validated state for final merge verification.
- Independent mathematical review checked signed radicands, repeated
  square classes, zero roots, the empty family, the essential nonzero
  divisor, the single natural witness, both denominator conditions, all
  fourteen capital substitutions and six radicands, the twelve-coordinate
  assignment, and the prime-2 boundary case. The common-weight construction
  is the one proved here. The refined weights, five-square replacement,
  and printed degree 13697 remain unproved; the source-level arithmetic
  in `RELATION_COMBINING_FRONTIER.md` is not a Lean degree certificate.
- Upstream was merged through
  `3feebaf5dfada7f1dd37d3fd0d7afdb1bf833076` before this consolidated build.
  The merge preserved all thirteen new proof/audit source files
  byte-for-byte. Its 1980 article and certificate work is a separate
  contribution. This formalization batch changes no article TeX or PDF
  and claims no PDF rebuild or remote CI run. The editorial notes retain
  the proof and domain clarifications; no new article equation error was
  found. The broader six-article formalization remains incomplete.
  The final publication merge additionally incorporates upstream
  `40efe15` (the separate 106-operation certificate). Its changes are
  confined to the README, editorial notes, and 1980 proof/checker artifacts.
  All 137 validated source/configuration files remain byte-for-byte
  unchanged in the working tree; their staged contents also match after
  Git newline normalization. No additional Lean build is claimed for
  that documentation-only integration.

## Validation — 2026-09-14, refined relation combining, exact-degree primes, and Theorem 3

- All 43 affected project modules passed serialized Lake targets before
  one consolidated `lake build`, which completed successfully with
  **3579 jobs**. The integration includes the incoming 1980 `IndexCode`
  and `Theorem5` modules and their 1982 dependencies. The `IndexCode`
  import was narrowed from `Mathlib` to `Mathlib.Tactic`; its statement
  and proof are unchanged.
- The new refined arithmetic, polynomial, bound, semantic, and degree
  modules pass, as do the growth criterion, both refined prime-polynomial
  constructions, concrete degree certificates, exact positive-padding
  construction, and `PrimeZeroTest`. No new module emits a warning.
  Existing modules retain their linter and deprecation warnings; this is
  not a warning-free or clean-cache build claim.
- `lake env lean Computability/HilbertTenthProblem/Lean/checks/RelationCombiningAxioms.lean` passed all **37**
  checks. `lake env lean Computability/HilbertTenthProblem/Lean/checks/RefinedRelationCombiningAxioms.lean`
  passed all **50** checks, including Theorem 3 and the incoming 1980
  endpoints. Every reported dependency belongs to `propext`,
  `Classical.choice`, or `Quot.sound`; no project mathematical axiom or
  `sorryAx` occurs.
- A nested-comment and string-aware scan covers **148 library Lean
  files**: 134 project modules, twelve vendor proof modules, and two
  umbrellas. It finds no code token `sorry`, `admit`, `axiom`, or
  `native_decide`. Every project module occurs exactly once in the
  umbrella imports. SHA-256 receipts record the raw and LF-normalized
  contents of all **153** library, audit, and Lean configuration files.
- Independent source review checked divisor/dividend positivity,
  unconditional root majorants, signed/repeated/zero radicals, the empty
  family, the five-square growth interface, the prime-2 case, and the
  twelve natural coordinates. Theorem 3 explicitly checks its natural
  exponent, `0^0=1`, failed tests, and parameter zero.
- The unpadded combined-equation bounds are **13376** and **6848**;
  the associated prime-polynomial bounds are **26753** and **13697**.
  Exact degree **13697** belongs to the positive-padding construction.
  The common-weight estimates 148864 and 297729 remain source-derived.
- All 23 local Markdown links in the five maintained documents pass.
  This milestone changes no article TeX or PDF. The parallel 1980
  article/certificate work remains a separate contribution; this receipt
  claims no PDF rebuild or remote CI run.
- The proof checkpoint is `e8ac254`. Publication merge `93361d7`
  incorporates `origin/main` at `02f1bffcf6f11cbb186e4cca8fb762ca2b7091a5`.
  Those incoming changes concern the README, editorial notes, and the
  separate 1980 article/certificate artifacts. All 153 validated files
  remain byte-for-byte unchanged in the working tree and match the index
  after newline normalization. The source/import scan and all 23 local
  links pass after the merge; no additional Lean build is claimed for
  that source-preserving integration.

## Validation — 2026-09-14, abridged 1980 scope and single-parameter reduction

- The retained 1980 numbered scope is Theorems 1–3 and the proved
  `(58,4)` case of Theorem 4. The other fifteen reported pairs and
  Theorem 5 are explicitly excluded by the project owner. The
  [statement audit](PAPER1980_AUDIT.md) checks the printed systems,
  quantifier order, positive-input convention, admissible codes, and
  degree after fixing the three index parameters.
- `Paper1980/SingleParameter.lean` proves that adjoining the literal
  code equation preserves each system, using one positive code chosen
  before all inputs. It adds three positive witnesses, giving 15, 17,
  and 31. No decoder, computable-enumeration equivalence, or unchanged
  witness-count assertion is included.
- `Common/DiophantineFunctionPolynomial.lean` proves Putnam's
  positive-value construction for any function with a Diophantine graph.
  It includes zero outputs and an empty original witness family. It
  supplies finite witnesses without a numerical bound; 1976 Theorem 4's
  prime-graph premise and the 14-witness refinement remain open.
- Both new modules passed focused Lake targets, followed by one
  consolidated `lake build`: **3581 jobs**, with all 136 project modules
  imported exactly once. The new modules emit no warnings; existing
  linter and deprecation warnings remain elsewhere.
- `lake env lean Computability/HilbertTenthProblem/Lean/checks/Paper1980Axioms.lean` passed **15** transitive
  dependency checks, and
  `lake env lean Computability/HilbertTenthProblem/Lean/checks/DiophantineFunctionPolynomialAxioms.lean` passed
  its one check. Every dependency belongs to `propext`,
  `Classical.choice`, or `Quot.sound`. No new axiom is introduced.
- A nested-comment and string-aware scan of all **150 library Lean
  files** finds no code token `sorry`, `admit`, `axiom`, or `native_decide`.
  SHA-256 receipts record raw and LF-normalized contents of **157**
  library, selected audit, and Lean configuration files for publication
  verification. Independent review checked the zero-output and
  empty-witness cases, index positivity, and fixed-parameter order.
- The READMEs and editorial notes record the scope decisions and the
  superseding no-new-axioms policy. This proof milestone changes no
  article TeX or PDF; no new article equation error was found. The
  broader six-article goal remains incomplete.
- The proof checkpoint is `a90f9d3`. Publication integrates `origin/main`
  through `d5d5120e74ca73bcae0866269b922f513cf1f4cb`, including the
  separate article and operation-certificate work. The conflict-free
  merge preserves all **157** validated files byte-for-byte in the
  working tree and matches their staged contents after newline
  normalization. The source/import scan and all **41** local Markdown
  links across six maintained documents pass after integration. No
  additional Lean build, local review of the incoming PDF, or remote CI
  run is claimed for this source-preserving merge.

## Validation — 2026-09-14, MRDP in both directions and further 1976 theorems

- `Diophantine.mrdp_iff` proves the full equivalence between Mathlib
  `REPred S` and existence of one integer polynomial with finitely many
  natural witnesses, uniformly for every natural input including zero.
  `mrdp_dioph_iff` states the equivalence with Mathlib `Dioph`; `mrdp`
  retains the forward interface. The proved finite-trace/bounded-evaluator
  bridge supplies the difficult direction, finite support supplies the
  ordinary polynomial, and a new primitive-recursive witness search
  proves the converse. The [MRDP guide](MRDP.md) records the proof chain.
- The 1976 Theorem 4 now has a proved nth-prime graph and a fixed finite
  polynomial from Putnam's construction. The separate fourteen-witness
  refinement remains open. Theorem 5 has an acyclic signed certificate
  with **40 addition and 47 multiplication checks**, with final comparisons
  equivalent to Theorem 2.12 and certificate existence equivalent to
  primality, including 2. Independent source comparison matches every
  one of the **87 instructions** and **14 system comparisons** to the JSON.
- Theorem 4.1 retains complex coefficients and includes zero variables.
  Rational coefficient descent and positive denominator clearing are
  proved, and the progression argument cancels the denominator in the
  integers without assuming it coprime to the selected prime. Independent
  source/API reviews found no statement-fidelity or circularity issue in
  the MRDP or certificate constructions.
- The proof checkpoint is `5486843`. Integration through upstream
  `f7f40444ebf61c34ca70eb409e67f987fffbfca3` is recorded by `20fd7d8`,
  including the parallel article artifacts and the five modules
  `PellInt`, `System99`, `Circuit`, `PellDoubled`, and `PellExponent`.
  The only modification to their mathematical source is narrowing the
  import of `System99` to `Mathlib.Data.Int.Basic` in `ad7a7ed`; its
  definitions are unchanged. The former whole-Mathlib import caused a
  compiler process to reach about 8 GB of private memory, so that build
  was stopped and restarted after the import fix.
- The consolidated build after the import fix passed **3595 jobs**.
  After the final upstream integration, the consolidated `lake build`
  passed **3596 jobs** with all **149 project modules** imported exactly
  once. Existing linter/deprecation warnings remain in older and incoming
  modules. All eight new modules of the proof checkpoint also passed
  focused Lake targets.
- The new transitive dependency audits pass **21 checks**:
  `checks/MRDPAxioms.lean` (**11**), `checks/NthPrimeAxioms.lean` (**2**),
  and `checks/PrimeCertificatesAxioms.lean` (**8**). Every reported axiom
  belongs to `propext`, `Classical.choice`, or `Quot.sound`. The MRDP
  proof and its dependencies were unchanged by the upstream merges.
- A nested-comment and string-aware scan of all **163 library Lean
  files** finds no code token `sorry`, `admit`, `axiom`, or `native_decide`.
  Raw and LF-normalized SHA-256 receipts record **173** library, selected
  audit, and Lean configuration files. All **56 local Markdown links**
  across seven maintained documents pass. Git publication checks compare
  the validated sources with the working tree and index.
- These proofs required no article equation correction. The editorial
  notes record their source conventions and proof boundaries. Incoming
  article TeX/PDF artifacts were merged from the parallel work; this
  receipt claims no local rebuild or visual review of those artifacts
  and no remote CI run. The 1980 exclusions remain in place. The broader
  six-article goal remains incomplete, including the 1976 fourteen-witness
  refinement and Theorems 4.2–4.4.
- Publication also integrates upstream
  `7ca55aac6cf99ca27d75c9750cd913f1ac847604`, which changes only article
  notes and certificate artifacts. This conflict-free merge preserves all
  **173** validated source/configuration files byte-for-byte and matches
  their staged contents after newline normalization. The source/import
  scan and all **56** local links pass again; no additional Lean build is
  claimed for this source-preserving integration.

## Validation — 2026-09-14, first existing-code cleanup

- The cleanup checkpoint is `e47f5d0`. It extracts a shared integer
  square-test lemma and its full positivity equivalence, and equality of
  halted runs from arbitrary initial configurations. Existing clients keep
  their hypotheses and interfaces. The square test generalizes the former
  private positive-multiplier result to a nonnegative multiplier.
- Signed relation combining specializes the existing unsquared arithmetic
  lemmas; finite Godel coding specializes the stronger lower-bound theorem.
  Primitive-recursive composition, two-step induction, and bitwise order
  use their existing general interfaces. Comments now state the actual Pell
  shift identity, retain the binomial-digit hypothesis `k ≤ n`, and describe
  both directions of MRDP. The [code review](CODE_REVIEW.md) gives details.
- A comment-aware comparison preserves **185 existing public theorem/lemma
  statement headers** across the fourteen edited mathematical modules,
  including inline attributes. Independent source review found no change
  to the polynomial definitions, witness counts, degree bounds, or theorem
  meanings. Including the new helpers and expanded comments, the cleanup
  removes **91 library lines**; documentation and audit drivers are separate.
- All twelve focused module/family targets passed. The first consolidated
  attempt had standard-library object-load failures in nine modules while
  free physical memory fell below 500 MB. The installed Lake did not use
  `LAKE_JOBS=1` to limit the compiler fan-out. With `LEAN_NUM_THREADS=1`
  set before launching a fresh Lake process, the recovery build passed
  **3599 jobs**. No mathematical source or library object was changed to
  recover from those failures. The failed and successful logs are retained
  separately; existing linter/deprecation warnings remain.
- The recovered snapshot includes the upstream merge `50a874c` through
  `37c8491`, plus an umbrella import for the incoming `System95` module.
  All **152 project modules** are imported exactly once. A code-token scan
  of **166 library Lean files** finds no `sorry`, `admit`, `axiom`, or
  `native_decide`. Source, selected audit, and configuration hashes record
  **177 files** for this snapshot.
- `checks/CodeCleanupAxioms.lean` passes **25 transitive checks**, and
  `checks/MRDPAxioms.lean` repeats all **11** MRDP checks. Across these
  **36 checks**, every reported axiom belongs to `propext`,
  `Classical.choice`, or `Quot.sound`; some elementary helpers use none.
  This is local kernel and dependency evidence, not a remote CI receipt.
- Further article formalization remains paused. The next polynomial
  renaming, degree-bound, and sign-flip simplifications are uncompiled
  drafts outside the library at this checkpoint. Incoming article TeX/PDF
  artifacts were preserved from the parallel work; this receipt claims no
  local rendering or visual review of those artifacts. The agreed 1980
  exclusions remain unchanged.
## Validation — 2026-09-14, integrated proof cleanup and generalization

- MRDP remains proved in both directions, including input zero and an empty
  witness tuple. The final cleanup retains all existing public interfaces.
  The first batch is recorded in `e47f5d0`; the polynomial-helper batch is
  recorded in `a69e976`, with its checked assignment adapters in `e55f134`.
  The [review guide](CODE_REVIEW.md) describes the changes and their scope.
- The new polynomial helpers support arbitrary variable and witness types,
  arbitrary maps into commutative semirings, arbitrary target values, and
  finite sums of arbitrary powers. The sign-flip helper supports arbitrary
  variable types and commutative rings. Their existing quartic and
  relation-combining clients preserve polynomial definitions, residual order,
  coordinate maps, witness counts, and degree bounds.
- A comment-aware comparison preserves **259 existing public theorem/lemma
  headers in 21 modules** across the two cleanup batches and the incoming
  Pell proof repair. Independent semantic and literal diff reviews also pass.
  The quartic adapters compare assignment functions pointwise, avoiding
  reliance on conversion between imported and local generated matchers.
  Both quartic modules passed focused Lean checks before the final build.
- The consolidated `lake build` at `e38fcd6` passes **3609 jobs** with
  `LEAN_NUM_THREADS=1`. All **162 project modules** are imported exactly once.
  The source scan covers **176 library Lean files** and finds no code token
  `sorry`, `admit`, `axiom`, or `native_decide`. Raw and LF-normalized hashes
  record **188** library, selected audit, and Lean configuration files.
  All **78 local Markdown links** across eight maintained documents resolve.
  Earlier failed attempts remain separate from the final successful log;
  existing linter and deprecation warnings remain.
- Fresh transitive axiom checks pass **57 declarations**:
  `checks/CodeCleanupAxioms.lean` (**25**), `checks/MRDPAxioms.lean` (**11**),
  and `checks/PolynomialCleanupAxioms.lean` (**21**). Every reported axiom
  belongs to `propext`, `Classical.choice`, or `Quot.sound`. This includes
  all three public MRDP statements, the cleanup helpers and clients, the
  repaired Pell proofs, and six representative incoming support endpoints.
- The integrated mathematical sources include upstream
  `3e3130ed7ed1332140bf84d83a78cc13f7654517`. Comments now include the mask's
  digit-width and positive-radix-exponent hypotheses, the relaxed Pell
  positivity hypotheses, and the positive-input boundary of the system-level
  Pell result. The window overview no longer claims an absent `paired_zero`
  declaration. These are comment corrections; the incoming theorem statements
  and proof boundaries are preserved.
- Merge `c4938da` additionally integrates upstream
  `eac3c5f3b2d3ecd798239b70cc52cffae50c78b0`, containing only article exploration
  notes and Python/JSON artifacts. All **188** validated source/configuration
  files remain byte-for-byte unchanged and match the index after newline
  normalization. No additional Lean build is needed for this integration.
- Further article formalization remains paused. The 1980 Theorem 5 remains
  intentionally excluded; Theorem 4 remains in its agreed abridged form.
  Incoming TeX/PDF artifacts are preserved from the parallel work. This
  receipt claims local kernel and dependency validation, without a local
  article render, visual review, or remote CI run.

## Validation — 2026-09-17, 1974 (3) and the numerical table, 1984 §4–§5

- The consolidated `lake build` passed **3769 jobs** with no errors, after the
  session's new modules `Paper1974/Doubling.lean`, `Paper1984/FastSoundness.lean`
  and `Paper1984/NDet.lean` were registered in `Diophantine.lean`.
- Axiom audits of the new endpoints — `Jones1974.sc_lt_sigma`,
  `Jones1974.table_two`, `table_three`, `table_six`, `JM1984.RM.xaccepts_iff`
  and `JM1984.RM.naccepts_iff` — report only `propext`, `Classical.choice` and
  `Quot.sound`.
- (3) `SC(n) < Σ(3n)` follows the editorial construction: `n` simulating states,
  `2n` helper slots of which one is free (a halting machine has a halting rule)
  and serves as the final state, exactly `3n` states in all. The counting
  injects the actively scanned squares into the ones of the final tape, which
  also carries the appended one, so the score is at least `SC(n) + 1`.
- The table rows `n = 2, 3, 4, 5, 6` are witnessed by explicit machines checked
  by kernel evaluation; the search for the 6-state witness (36 ones in 570
  shifts) and the exhaustive 3-state search (6 ones, 7 squares, 21 shifts) were
  run outside Lean and are evidence for the *upper* halves only, which remain
  unformalized.
- The 1984 system for the fast commands is now an equivalence in both
  directions, and §5's nondeterministic `BRANCH` is arithmetized with (52). The
  NP characterizations (53), (54) still rest on Adleman–Manders and are not
  formalized.

## Validation — 2026-09-21, concise MRDP proof transplanted into the article library

- `Common/MRDPCore.lean` contains the same **391-line** readable proof as
  the canonical `mrdp/MRDP.lean`, retaining its comments and `MRDP` namespace.
  Both files have SHA-256
  `c6f8b993f95be28b1f18e21cb82442c61d4011907f73f6725ac2f15486864c78`.
  The standalone mathematical source was not changed by this transplant.
- `Diophantine.mrdp` now forwards directly to `MRDP.mrdp`.
  `rePred_dioph` adapts its finite polynomial to the existing Mathlib `Dioph`
  interface, redirecting the article representations through the new proof.
  The scalar primitive-recursion interfaces are short adapters to
  `MRDP.primrec_diophFn`. The seven existing public signatures in these three
  modules are unchanged, and the existing converse remains in place.
  `NthPrimeGraph.lean` now imports its pairing interface explicitly.
- The general trace interfaces and the twelve vendored `PAListCoding`
  modules remain independently available. They are no longer prerequisites
  of the MRDP or article-facing RE proofs. The original extraction was
  introduced in `7a2c8b3`, from source revision `dc9aa085`; its historical
  manifest recorded twenty source modules.
- A complete `lake build` from `Lean/` passed **3773 jobs** with no errors.
  This includes the umbrella, the modified MRDP and scalar interfaces, the
  nth-prime polynomial, and the 1978/1982/1980 representation clients.
  Existing linter and deprecation warnings remain in unchanged modules.
- The parent audits passed **78 entries** in total:
  `MRDPAxioms.lean` (**18**), `RecursivelyEnumerableAxioms.lean` (**33**),
  `CodeCleanupAxioms.lean` (**25**), and `NthPrimeAxioms.lean` (**2**).
  Every reported axiom belongs to `propext`, `Classical.choice`, or
  `Quot.sound`; `Diophantine.two_step` is axiom-free. These entry counts
  include endpoints repeated across audit files.
- The strengthened `MRDPAxioms.lean` rejects any unexpected axiom
  transitively and independently restates all three public MRDP contracts.
  All three statement checks passed, including natural input zero, natural
  witnesses, and one finite polynomial chosen before the input.
- The unchanged standalone `checks/Axioms.lean` also passed its axiom and
  endpoint guards. `python tools/check_mrdp_sync.py` confirmed byte equality
  of the two proof files; the script's success, mismatch, and missing-file
  outcomes were also exercised. The Lean module and check sources captured
  by the validation run remained unchanged throughout its eight stages.
- The reusable dependency audit traversed defining modules under both
  `Diophantine` and `PAListCoding`, with roots `Diophantine.mrdp`,
  `Diophantine.mrdp_iff`, and `Diophantine.rePred_dioph`. Its combined
  closure contains **60 local declarations**, **963 boundary declarations**,
  **zero unresolved source owners**, and **zero PAListCoding dependencies**.
  Boundary declarations are where this source-extraction traversal stops;
  the axiom checks above traverse the proof assumptions independently.

  | Root | Local declarations | Boundary declarations |
  |---|---:|---:|
  | `Diophantine.mrdp` | 47: its wrapper and 46 core declarations | 894 |
  | `Diophantine.mrdp_iff` | 56 | 943 |
  | `Diophantine.rePred_dioph` | 51 | 925 |

The [MRDP guide](MRDP.md) records focused and full reproduction commands,
source ownership, and synchronization. Local logs, source hashes, and the
combined dependency graph are in `.lake/mrdp-transplant/`. This receipt
records local Lean validation; it makes no remote-CI claim and leaves the
agreed article scope unchanged.
