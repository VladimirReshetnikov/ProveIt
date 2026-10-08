# Claim and evidence ledger

This ledger states what **Modular Boundary Responses for Unknot Recognition** establishes, implements, measures, and leaves open. It accompanies the [article](article/unknot_modular_boundary.pdf) and [integration instructions](README.md). The source and literature audit is dated **8 October 2026**.

The general mathematical arguments are proofs in an AI-assisted working paper. Finite tests and independently coded arithmetic checks provide additional evidence; they do not constitute formal verification of the entire recognizer or peer review of the paper.

## 1. Baseline and attribution

The integration base is upstream ProveIt commit `8a95834940cf77cdab1b39571ffc102ca8b6bede`. The benchmark records the distinct local materialization commit `3179d245a6752749c09d4fe79c018c79d2209c2d`. `provenance.json`, the recorded source hashes, and `MANIFEST.sha256` identify these roles. The benchmark's Git field alone does not identify every uncommitted addition that was timed.

The following ingredients predate this continuation:

| Ingredient | Attribution and scope |
| --- | --- |
| Relative Khovanov complexes, tangle composition, delooping, and local cancellation | Bar-Natan's [2005 tangle paper](https://arxiv.org/abs/math/0410495) and [fast-computation paper](https://arxiv.org/abs/math/0606318), together with the maintained implementation. |
| Khovanov rank as an unknot detector | [Kronheimer–Mrowka](https://doi.org/10.1007/s10240-010-0030-y), with the coefficient-field interpretation used by the maintained recognizer. |
| Marked four-residue Euler obstruction and singular-safe rational terminal kernel | ProveIt report 26 and the later boundary-reuse synthesis and research prototype. |
| Direct integer determinant factoring and budgeted Euler fallback | Maintained ProveIt modules and synthesis at the pinned revision. |
| Boundary response and grove formulas | Established literature, including [Kenyon–Wilson](https://arxiv.org/abs/math/0608422). The signed singular case requires the separate algebraic argument supplied here. |
| Modular determinant computation and bound-certified CRT | Established exact linear algebra, including [Dumas–Urbańska](https://arxiv.org/abs/cs/0511066v5). |

The contribution is an exact terminal count for the checked representation, a maintained modular continuation of the existing rational approach, explicit minimum-norm and threshold-completion proofs, resource-aware integration, and comparative evidence. The article does not assert historical priority for every elementary algebraic lemma.

## 2. Mathematical hypotheses

The recognition guarantee concerns a **validated classical knot diagram** and a genuine proper scan prefix. Its relative complex must be obtained by the marked-compatible tensoring, delooping, and cancellation operations described in the article and implemented by the maintained scanner. An arbitrary matrix satisfying `d² = 0` is insufficient.

Completed matchings must cover the actual frontier, preserve the inherited checkerboard data required by the optional representation, and pass the spherical rotation-system check. The implementation can decline this optional geometric representation and continue through fallback. The determinant theorem alone is not a theorem that every abstract pairing encodes a valid classical completion.

Let $\mathcal C_a$ denote whole differential components of the relative complex, `m_a > 0` their integer multiplicities, and `x_a ∈ Z⁴` their completed four-residue Euler vectors. Each vector is formed **after aggregating all objects of its component**, with the recovered quantum shifts and homological signs. The existing integer obstruction is

$$
B_4 = \sum_a m_a\lVert x_a\rVert_1
\le \dim_{\mathbb F_2}\widetilde{Kh}(K;\mathbb F_2).
$$

The scalar `C_a` used below is a certified bound on each coordinate of `x_a`.

## 3. Proved mathematical refinements

### 3.1 Exact terminal count and singular response

For the checked cut-face suffix geometry with `b > 0` frontier darts, the number of black open face fragments is exactly

$$
t=b/2.
$$

At each validated odd prime, symmetric elimination uses one- or two-coordinate pivots and retains the radical of the interior block. Write `r` for its nullity and `q` for the number of ungrounded terminal blocks in a query. The residual query matrix has dimension `r + q`. If `r > q`, the quotient cofactor is zero; otherwise

$$
r+q\le 2q\le 2(t-1)=b-2.
$$

This remains valid when reduction modulo a prime increases the interior nullity. A modular zero is a zero residue of the correct integer cofactor, not evidence that the integer itself vanishes. Empty frontiers use the separately handled grounding case. The bound `b - 2` is a bound on the final query matrix; dense preparation and all other stored data remain part of the resource cost.

**Evidence:** [Article Section 3](article/sections/03_geometry.tex), `boundary_tait.py`, `modular_response.py`, response tests, and the actual-diagram audit. The audit includes residual nullity two and 198 radical-dimension zero cases. The favorable timing family contains no singular modular interiors.

### 3.2 Sound, monotone integer lower bounds

For an odd product `M` of distinct validated primes, let `a_a` be the exact integer coordinate sum of `x_a`. Define

$$
F_M(z,a)=\min\{\lVert y\rVert_1:y\in\mathbb Z^4,\ y\equiv z\pmod M,\ \textstyle\sum_j y_j=a\},
\qquad
L_M=\sum_a m_aF_M(x_a,a_a).
$$

Then `0 ≤ L_M ≤ B_4`. Refining by divisibility, `M | M'`, cannot decrease the lower bound. Consequently `L_M > 1` is a deterministic knottedness obstruction, including when primes are selected heuristically. The implementation uses a fixed default prime, not probabilistic stabilization of reconstructed coefficients.

The auxiliary primes compute residues of **integer Euler data**. They do not change the Khovanov coefficient field from F₂. Norms from different primes are not added, and norms of proper subsets of a differential component are not substituted for the whole-component norm.

**Evidence:** [Article Sections 2](article/sections/02_euler.tex) and [4](article/sections/04_modular.tex), `modular_shadow.py`, the diagram audit, and positive-claim replay through the old integer observer.

### 3.3 Explicit minimum with a known coordinate sum

The article gives an exact formula for `F_M`. Starting with balanced representatives, it allocates the required signed modulus steps using the largest available first-step discounts. A minimizing lift requires `O(d log d)` comparisons and integer arithmetic for dimension `d`; it does not iterate once per unit of a potentially large lift coefficient. The application has `d = 4`.

A feasible lift alone does not establish a lower bound: its norm might exceed the true minimum. The replay verifier separately checks the minimum, and a corruption test rejects a feasible but nonminimal lift.

**Evidence:** Theorem “Minimum norm with a known sum” in [Section 4](article/sections/04_modular.tex), `modular_lattice.py`, the separately coded replay calculation, and [the independent arithmetic audit](verification/arithmetic_audit.py).

### 3.4 Deterministic threshold completion

Suppose each component vector satisfies `|x_{a,j}| ≤ C_a`. For an integer threshold `T ≥ 0`, the sufficient condition

$$
M>\max_a\left(C_a+\left\lfloor\frac{T}{2m_a}\right\rfloor\right)
$$

implies `L_M > T` if and only if `B_4 > T`. In particular, **`M > max_a C_a` suffices at threshold one**. This is a Boolean comparison theorem; it does not reconstruct all large coefficients.

The strict inequality matters. The abstract integer vector `(M, -M, 0, 0)` has exact sum zero and is invisible modulo `M`. This is an algebraic counterexample to replacing the strict condition with equality; no claim is made that every such prescribed vector occurs in a knot prefix.

After the earlier exact Euler check has established `sum_a m_a |a_a| ≤ 1`, the exact-sum minimum and the ordinary balanced-residue norm reject exactly the same inputs at threshold one. The known sum improves the sufficient **completion condition**, not the set of additional threshold-one detections in that situation.

**Evidence:** Both completion theorems and the “No extra threshold-one rejection after the Euler check” proposition in [Section 4](article/sections/04_modular.tex), lattice tests, and the independent threshold audit.

### 3.5 Explicit coefficient and modulus-bit bounds

For a completed suffix with `n ≥ 1` crossings and no extra crossing-free circles supplied outside its matching, the per-object vector satisfies `||σ||₁ ≤ 2^(n−1)`. If a component contains `s_a` represented objects, a valid coordinate bound is

$$
C_a=\sum_{o\in\mathcal C_a}
\left\lfloor\frac{|a_o|+2^{n-1}}2\right\rfloor
\le s_a2^{n-1}.
$$

Thus `O(n + log(s_max + 1))` modulus bits suffice for threshold-one agreement with the integer observer. The object count is a represented-complex parameter; this bound does not show that it is small.

The current API accepts a finite palette of distinct odd primes below `2³¹` and defaults to `(65521,)`. It reports whether the sufficient completion inequality was reached. The article supplies a deterministic asymptotic prime-supply argument, but the implementation does not automatically generate an unbounded supply of larger primes.

**Evidence:** [Article Section 5](article/sections/05_complexity.tex), certified coordinate accounting in `modular_shadow.py`, prime validation, and audit comparisons with exact component vectors.

### 3.6 Prime exposure and conditional complexity

If `B_4 > 1` is already present and coordinates are bounded by `H`, an inconclusive prime must divide `x(x−1)(x+1)` for a suitable coordinate with `|x| ≥ 2`, unless all coordinates are `0, ±1`, when every odd prime detects the obstruction. This bounds the number of inconclusive primes in a pool bounded below by a specified prime size. It neither guarantees the existence of an obstruction nor bounds the cost of reaching its prefix.

The conditional quasi-polynomial proposition states that a sufficient-modulus modular observer preserves a quasi-polynomial bound **if** the required relative complexes, all objects and morphisms, and the decisive scan work already have suitable constructive quasi-polynomial bounds. That representation hypothesis is unresolved for general inputs. A polylogarithmic frontier only bounds possible oracle keys; many differential generators can share one key.

**Evidence:** Prime-exposure proposition in [Section 4](article/sections/04_modular.tex) and the explicit cost account and conditional proposition in [Section 5](article/sections/05_complexity.tex).

## 4. Implemented recognition and replay semantics

The new backend is selected with `backend="shadow-modular"` or `--backend shadow-modular`. The existing default remains `standard`.

| Event on the modular raw path | Meaning |
| --- | --- |
| A verified weighted modular lower bound exceeds one | Sound `KNOTTED` observation. Processing may stop after distinct whole components already supply the obstruction. |
| A small bound with certified threshold completion | The existing integer Euler observer would also fail to reject at this prefix. Scanning continues. |
| A small bound after exhausting the finite palette | An incomplete negative observation. Scanning continues. |
| Local determinant-work or observation allowance exhausted | The prescribed Euler/capped-scan fallback continues. A partially constructed response is not cached as complete. |
| Global time or object allowance exhausted | The public recognizer returns `UNKNOWN`. |
| Final complete rank calculation identifies the unknot | `UNKNOT` comes from the rank calculation, never from small modular residues. |

Positive raw claims can be replayed with `replay_modular_shadow`. Replay reconstructs the prefix with the maintained `ComponentScan`, checks whole-component identity and grading, and recomputes integer completion vectors with the older `ClosureShadow`. It checks CRT products, residues, exact sums, coordinate bounds, multiplicities, and the minimum-norm claim. The modular response and production lattice minimizer are absent from that observer-arithmetic verification path.

This is **full prefix replay with independent observer arithmetic**. It shares the maintained scanner, can require comparable prefix work, and does not constitute a short standalone NP certificate or an independently formalized scanner. Runtime counters and timing metadata are outside its authenticated scope.

The implementation has cooperative production deadlines. The benchmark adds an in-process POSIX signal timer. Neither is described as a general worst-case constant-time interrupt mechanism for every underlying operation.

## 5. Recorded validation

| Validation record | Observed result | Scope limit |
| --- | --- | --- |
| [New modular suite](verification/modular_tests.log) | 31 tests pass across response, shadow integration, and replay modules. | Finite examples, including singularity, exceptional primes, cancellation, and tampering. |
| Response test comparisons | 1,964 randomized quotient comparisons with independent modular and integer determinant routines. | Finite arithmetic cases, not an exhaustive proof over all matrices. |
| [Independent arithmetic audit](verification/arithmetic_audit_result.json) | 33,300 minimum-norm cases and 1,496,340 weighted threshold cases pass. | The script imports no production modular code; the general theorem still needs its proof. |
| [Actual-diagram audit](reproducibility/ProveIt/Topology/UnknotRecognition/fast/results/modular_audit.json) | 138 diagrams, 868 proper prefixes, 2,516 actual matching completions, 15,096 modular vectors, and 50 positive replays checked. | At most nine crossings per diagram; independent full reduced F₂ cubes are exponential. |
| Small-prime audit | Prime three misses 70 existing obstructions; no false positive is observed. The six-prime adaptive palette certifies all 868 recorded threshold comparisons. | This finite palette is not claimed to suffice for arbitrary input sizes. |
| [Broader maintained suite](verification/full_tests.log) | 708 tests discovered: 704 pass, three optional-Regina skips, one inherited worker error. | This run included the first 21 modular tests; the ten replay tests were added later and pass in the separate 31-test run. |

The broader-suite error is documented in [the inherited worker issue note](verification/normal_surface_baseline_issue.md) and its [machine-readable record](verification/normal_surface_baseline_issue.json). On the recorded CPython 3.12.14 POSIX runtime, repeated timed communication retains an input buffer but stops scheduling pending stdin writes. The unchanged baseline worker reproduces the failure, while uninterrupted communication with the same child and payload succeeds. This is a separate optional-worker defect, not a passing test or a modular-observer regression. No fix to that worker is included.

## 6. Recorded performance claims

The [benchmark JSON](reproducibility/ProveIt/Topology/UnknotRecognition/fast/results/modular_benchmarks.json) contains five shuffled paired rounds, one excluded warm-up per arm, an identical integer control, fresh constructors, and all individual samples. Arithmetic timings include geometry and response setup. Correctness checks and digests are outside timing. Ratios are medians of within-round old/new time ratios.

The supported numerical conclusions are:

1. **Repeated suffix arithmetic can improve substantially.** For 47 genuine interior vertices and 200 actual prefix matchings, the modular evaluator is 26.666 times faster than maintained direct evaluation and 3.968 times faster than the earlier rational response. For 127 interior vertices and 50 queries, the respective factors are 10.743 and 10.218.
2. **Preparation can lose.** The all-terminal case favors both predecessors. Three interior vertices still favor the rational prototype. The 15-interior rational/modular comparison is close.
3. **No whole-recognizer gain is demonstrated on this corpus.** All seven raw scans and all seven deliberately disabled-filter pipeline comparisons favor the existing direct observer. Normal filters decide all seven inputs before a shadow observer is used.
4. **Censored pilots are not speed measurements.** At the largest size, direct 200-query pilots time out. A fresh 50-query workload supplies the reported complete paired comparison; the censored pilot supplies no ratio.
5. **Singular performance remains unmeasured here.** Every timed modular interior has nullity zero. Singular correctness is covered separately.

The benchmark records 24,200 repeated vector comparisons and 2,013 repeated status comparisons. These are validation-event counts, not distinct inputs. All completed modular vectors agree with integer and rational outputs modulo 65521, and all compared completed statuses agree. The 110 recorded source files remain identified by before/after hashes; `changed_sources` is empty. The later replay module is an additive verification artifact outside the timed path.

The runs were collected in a shared execution environment on CPython 3.12.14/Linux x86_64. Five repetitions support a local paired comparison. The figure's whiskers are observed paired minima and maxima, not confidence intervals. These observations do not establish an asymptotic speed ratio, a population-average improvement, or a reason to change the default backend.

## 7. Current external complexity claims

| Source examined | Accurate status used in this package |
| --- | --- |
| [Lackenby, March 2021 technical handout](https://people.maths.ox.ac.uk/lackenby/quasipolynomial-talk-oxford-compressed.pdf) | An announced quasi-polynomial algorithm with stated bound `2^{O((log n)^3)}`. The separate [Oxford seminar abstract](https://www.maths.ox.ac.uk/node/60914) states the stronger `n^{O(log n)}` expression. The package does not equate these exponents. |
| [Lackenby, arXiv:2607.23350v1](https://arxiv.org/abs/2607.23350v1) | A July 2026 hierarchy and certificate preprint. Its explicit iteration and encoding results do not supply a general quasi-polynomial construction-time theorem, and it leaves possible speed-ups to future work. |
| [Kelomäki–Schütz, arXiv:2601.02119v1](https://arxiv.org/abs/2601.02119v1) | A January 2026 preprint proving exponential behavior for the specified explicit scanning algorithms on certain three-braid closures and polynomial-time structural computation for three-braid Khovanov homology. This is not a lower bound on every unknot-recognition algorithm. |
| [Musick, arXiv:2609.06492v2](https://arxiv.org/abs/2609.06492v2) | A September 2026 preprint explicitly claiming polynomial-time unknot recognition. This package neither validates nor integrates that claimed algorithm and supplies no counterexample or disproof. Its compressed-state and geometric-minimality arguments merit a separate audit. |

The definite complexity statement made here concerns the maintained ProveIt recognizer and the supplied continuation: **a general quasi-polynomial guarantee has not been established by this work**. The source audit is not an assertion that every competing external claim has been completely assessed.

## 8. What further evidence would change the conclusion

The article's research agenda proposes twelve questions. The most consequential next milestones are:

- A scheduling change that improves total recognition time on a held-out corpus where earlier filters remain inconclusive, with setup, failed probes, refinement, and memory fully charged.
- An incremental response calculus that accounts for changing cut-face fragments and radical profiles as the suffix advances.
- A singular-safe block decomposition and a measured benefit from tighter coefficient bounds or better prime scheduling.
- A constructive continuation-compatible representation theorem controlling all generators, morphisms, sharing, and bit lengths through a decisive event.
- A bound on the work before the first decisive observation, or an efficiently verifiable compressed contraction with its own size and construction bounds.

The first three could establish practical acceleration. The last two address the unresolved mathematical work needed to turn an inexpensive observation interface into a general quasi-polynomial recognition result.
