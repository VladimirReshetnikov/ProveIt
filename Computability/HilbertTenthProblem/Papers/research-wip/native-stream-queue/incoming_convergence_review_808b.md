# Exact Convergence and Total Quadratic Semantics: review of 808b53ed8

Both complete mathematical articles and all six supplied compiler/checker/test files were read. The mathematical constructions are sound within the stated exact domains and finite/unbounded quantifier boundaries. No fixed numerical universal game or fixed-arity universal quadratic is emitted, and neither report changes the universal 87-operation bound. Three implementation boundaries need repair: the Bellman checker does not bind its scaled initial vector to the declared input, the total-quadratic compiler retains mutable catalogue/export containers and admits noninteger literals; and explicitly passing an integer scale to the optional counter loader can trigger floating-point underflow. Source-pinned repair patches were authored and tested in private copies; the incoming archives remain untouched.

This is an ordinary mathematical/source review with finite exact replay, not a proof-assistant verification, PDF layout audit or publication-priority assessment. Executable evidence and archive/member hashes are in `incoming_substrate_review_808b53ed8.json`. The portable original-source checker is `incoming_convergence_checks_808b.py`, exposing `verify(bellman_root, quadratic_root)`. The portable repair checker is `incoming_convergence_repair_checks_808b.py`, exposing `verify(bellman_root, quadratic_root, bellman_patch, quadratic_patch)`. Both pin source bytes, use temporary fixtures and restore their private import namespaces.

## Source boundary and replay

Safe private extraction rejected absolute paths, traversal, backslashes, duplicate member names and symlinks. All 33 extracted members were hashed and rechecked.

- `ProveIt_Exact_Convergence_Research.zip`: SHA256 `6e943e3301e5641b2306eff1cf979702a2584481c430d5561eed1c055b16a0ec`.
- `Total_Quadratic_Diophantine_Semantics.zip`: SHA256 `5b9fe27c520a2a1eeee14f197d8d62ffe9ff180c72ce7b6ee5645ddfc2f74c9b`.

Fresh private original replays passed:

```text
Exact_Convergence_Research:
  python code/run_checks.py
  python code/check_certificate.py artifacts/small_certificate.json --game artifacts/small_game.json
  python code/check_certificate.py artifacts/countdown_certificate.json --game artifacts/countdown_game.json
  python code/check_certificate.py artifacts/fixedpoint_certificate.json --game artifacts/fixedpoint_game.json

total_quadratic_semantics:
  python code/test_compiler.py
  python code/verify_exports.py
```

The Bellman author suite passes 26,077 assertions. The total-quadratic author receipt reproduces its 68,885 semantic assignments, 1,059 unique small fixed points, 1,663 compiled instances, 33,574 coordinate mutations, 320 Horn/general comparisons and other declared categories. All 12 regenerated game, polynomial and timeline exports are byte-identical. The author receipts differ only in Bellman's top-level `python` and the quadratic suite's top-level `runtime_seconds`. The Bellman CLI returns a polynomial value, not an `accepted` flag: all three delivered outputs were explicitly checked to have value zero.

Our independent checks additionally reconstruct **every coefficient of all three complete emitted Bellman polynomials** from the supplied game and declared initial input, including reset, scaling, reward, endpoint and product rows. This is stronger than replaying only their supplied zeros. Seventy-two additional small source reconstructions cover arbitrary rational discounts/rewards, all three endpoint modes and horizon zero. A separate rational recurrence and hand-written source interpreter verify 494 actual microsteps and paired-channel states. For the other report, 160 catalogues are compared with an independent queued-event implementation, all exact ledgers are checked, 480 complete off-zero natural polynomial evaluations agree with sparse expansion, and 54 Horn specializations agree. These finite checks support the proof audit; they do not prove universality or uniqueness by enumeration.

## Exact Convergence: proof and quantifier audit

The counter circuit correctly uses scaled reciprocal powers of two: `max(0,2c−s)` is exactly the zero test on valid encoded counters. One active branch updates the state and each counter; erasing halt removes every active branch and the clock. The source instruction set has independent jump targets, so it includes the undecidable CM2 instruction set rather than one of the weaker variants distinguished by Dudenhefner. The primary source's model and undecidability claim were checked. [Dudenhefner, FSCD 2022](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2022.16).

The stochastic construction pays all signed channels, delay copies, layer normalizers and input-register feedback. Both channels of each min/max gate use opposite owners. Full internal initialization is essential: the loader evaluates the one-step circuit, preventing a zero-filled output register from fabricating erasure. With period M and normalization K, the register formula `r_n=K^(-ceil(n/M)) F^ceil(n/M)(x)` holds at every microstep. The full-vector theorem then allows L additional pipeline steps after registers erase, including unused gates and initially halted inputs. The numerical fixed-point hit at 30 precedes the safe bound 32 without conflicting with it.

A uniform reset adds only a common scalar to general trajectories after positive rescaling. On the paired-channel subspace its mean is zero, yielding exactly

```text
Phi^n((w+1)/2) = 1/2 + (4^(-n)/2) S0^n(w).
```

Thus the unique, explicitly known limit is 1/2 and approximation is computably fast, while **finite exact attainment** from a supplied exact dyadic vector is c.e.-complete for a fixed game obtained by compiling a fixed universal program. Mixed-sign centered initial errors are essential; a nonzero one-sided error cannot vanish under full-support averaging. This is arithmetic of the whole vector, not a claim that a short sampled stochastic trajectory executes the universal computation. The ordinary initial value zero is also not the hard input family.

The paper does not print a numerical universal counter table/game. Its input loader contains reciprocal powers of two and one-step circuit evaluation; the bounded certificate receives the resulting integer numerators/denominator. Those steps are effective but are not a free ordinary-integer Diophantine loader with a charged global operation count. The delivered 128-state tables are one-counter examples. The complete certificate implementation bakes the supplied numerical input into coefficients; the article separately explains how its linear first-step dependence gives the horizon-indexed parameter schema.

The boundaries are correct: point-mass selectors have a finite value alphabet; chance-only whole-vector attainment is decided by `P^N e=0`; chance-only scalar equality is Skolem-equivalent with the game supplied as input. The comparison with one-player Bellman reachability does not remove the other owner from this construction or settle the remaining one-player fixed-point cases. The January 2026 revision's actual abstract supports the comparable-vector and dimension-two decidability statements. [Varonka–Watanabe v3](https://arxiv.org/abs/2502.19923v3). The cited July 2026 general Skolem implication remains conditional; it is not a general decision algorithm. [Luca–Ouaknine–Worrell](https://arxiv.org/abs/2607.15510). Ergodic-chain Skolem hardness is appropriately attributed as existing work. [Vahanwala](https://arxiv.org/abs/2305.04881).

For externally fixed T, complementarity gives one complete natural witness with `(N+2b)T` coordinates, `(N+b)T+e` affine squares and `bT` unsquared products. Ties force both gaps to zero. Reward forcing terms and target coefficients are actually emitted. Degree two relies on nonnegative product factors; arbitrary signed coordinates invalidate that argument. The state count and arity grow with the horizon, and the reward coefficients also depend on T. Quantifying an index before this changing family does not yield one fixed polynomial. MRDP supplies an existence-level fixed polynomial/quartic without transporting unique bounded witnesses or yielding an operation count. The nonexistence of a computable input-length bound on first attainment or a small witness box follows from c.e.-completeness.

## Bellman checker defect and repair

In original `code/check_certificate.py`, lines46–48 compare `input_numerators/initial_denominator` with the external game's initialization, but line64 begins replay at the separate, unbound `initial_numerators`. `witness_scale`, discount metadata and other duplicated fields are also not consistently bound.

A complete counterexample uses two identity action rows, discount1/2, zero reward, pair(0,1) and T=1. Generate the genuine certificate for input(0,0), then change only its declared `input_numerators` to(1,0) and supply a game declaring initial payoffs(1,0). The original checker returns polynomial value0 and `independent_game_check=True`, although the actual endpoint is(1/2,0), so the requested pair is unequal. The integer polynomial itself is an honest zero certificate for the different input; the false assertion is the checker binding.

The private patch `exact_convergence_input_binding.patch` validates exact metadata types/counts and enforces the scaling equations

```text
multiplier = lcm(denominator(reward), denominator(point target or 0));
witness_scale = initial_denominator * multiplier;
initial_numerators = multiplier * input_numerators.
```

It binds the actual game's state/owner/action counts, reward, reduced discount, probability denominator, optional input vector and optional observation. Base rows must themselves be stochastic with exact natural destination indices; the reset cannot hide an invalid base row. Product indices and the constant marker also receive exact-type checks. It preserves the original polynomial evaluator and witness-level trajectory semantics; it does not purport to certify universal source programs or redesign the emitted representation.

Original checker SHA256: `44ed5e089bd4e42ae4bf665d816fd92c1fb067cb6778702f7b36391d61230aec`.
Patched checker: `349fc50d5eb8d62287037e4116d95a18d48a8db1a2dde17d1211200febf20ce0`.
Patch: `697c2864262e9cc71dccf228aeba6b34c93140653846af496c0abcbbb513bb04`.

## Total Quadratic Semantics: proof and domain audit

The model is irreversible acquisition at exclusive sites, with persistent positive prerequisites, strictly positive delays, earliest offer and smallest-label ties. It is not arbitrary asynchronous nondeterminism, consumption, detachment, inhibition, stochastic kinetics or a multi-tile attachment model. Every site activates at most once. Following a maximum-time prerequisite strictly lowers activation time, so a critical chain cannot repeat a head; every activation time is a sum of distinct rule delays. Therefore the symbolic cap `1+sum(delays)` and the smaller unit-delay cap m+1 suffice without time unrolling.

The actual event output satisfies the capped equations, and induction on time below the cap forces any proposed output to match it. Inactive typed prerequisites use the cap rather than the occupied site's time, preserving exclusivity. The min/max and typed-mux slacks have unique extensions. Natural one-hot coordinates need no separate bit rows. Integer keys `(q+1)t+label` implement lexicographic order because time differences are integral; the paper explicitly avoids extending that encoding to arbitrary real times. Its separate real-delay phase theorem uses actual event comparisons, not this integer-key shortcut.

The exact timed counts are

```text
G = L+R0;
W = m(2q+3)+3D+3G+R;
affine squares = R+m(q+2)+2D+2G;
nonnegative products = 2D+G+m(q+1).
```

They count a fixed catalogue with delays as parameters; topology, glue data and the catalogue are not free numerical inputs. All product factors have nonnegative coefficients, giving orthant nonnegativity even away from zeros. Complete uniqueness is asserted for natural coordinates. Positive-coordinate translation preserves degree/uniqueness; four-square integer conversion gives finite fibers of degree at most four, rather than unique signed witnesses. The symbolic prefixes avoid a dense square of the complete delay sum. Huge delays change witness bit lengths, not the number of gates/sites. The 103-bit example and sparse monomial ledgers reproduce.

The one-label Horn reduction, the four-neighbor antichain incidence bound12, and the 37m/38m fixed-candidate allocations are correct within their fixed-labelled-candidate interface. The four-tile counterexample correctly shows that directedness does not permit multiple labels at an occupied site. Compatible-union and nested-box arguments rely on nonnegative singleton attachments. This is ordinary computational universality, not directed intrinsic universality; the primary literature distinguishes those properties. [Hendricks–Patitz–Rogers](https://arxiv.org/abs/1608.03036). Winfree's primary thesis supports the classical computational self-assembly premise; no new numerical universal tile table is implemented here. [Winfree's thesis](https://thesis.caltech.edu/1866/).

The finite real timing partition follows from the arrangement of finitely many distinct-head critical-chain forms. On each face the comparisons and complete label outcome are fixed. The resulting integer parameter sets have an explicit finite Presburger description; the semilinear terminology agrees with the primary theorem. [Ginsburg–Spanier](https://msp.org/pjm/1966/16-2/pjm-v16-n2-p09-s.pdf). The 2^m outcome lower bound concerns explicit constant-outcome lists, not arbitrary symbolic representations. Its nonmonotonicity example preserves the catalogue while changing a winning label and downstream route.

The displayed Horn rules exactly encode a deterministic TM using finite left/right lists and a growing term universe. Any finite grounding is decidable and has a total quadratic certificate; halting is `exists b: h_b=1`, while permanent nonhalting is `forall b: h_b=0`. A fixed existential integer polynomial for the latter would enumerate nonhalting and contradict undecidability. No computable sufficient accepting grounding-size bound exists. This is a valid obstruction to the negative universal query, not an obstruction to ordinary positive halting representations, and does not solve finite-fold or single-fold MRDP. Grounding can be exponentially large in its term-size bound, and varying the grounding changes arity.

## Quadratic input/export defects and repair

Original `quadratic_compiler.py` lines49–67 keep `Network.seeds` and `rules` without deep snapshots. For `seeds=[(0,1)]`, two sites/two labels and rule `(1,1)<-(0,1)`, compile the unit-delay model and its zero with output labels(1,1), times(0,1). Mutate the caller's list to `seeds[0]=(0,2)`. The old polynomial still evaluates to zero, but `compiled.net` now denotes labels(2,0), times(0,None). This is a mutable input-binding defect; the polynomial for the original frozen catalogue remains correct.

The same source permits fractional seed labels: `Network(1,2,((0,1.5),),())` compiles to a natural zero and reports label1.5, outside the declared alphabet. Boolean values also pass several `isinstance(int)` guards. `Certificate.export` lines127 and135 return the live parameter/witness lists and assignment mapping; clearing an exported witness list clears the compiler's allocator metadata.

The private `total_quadratic_immutable_inputs.patch` snapshots Rule literals/bodies and Network seeds/rules recursively, validates exact natural scalar fields and the positive label domain, checks Boolean options explicitly and rejects Boolean/float delays or natural assignments. Existing context validation still occurs on `validate`/compilation, preserving the supplied negative tests' construction pattern. Exports copy all externally mutable allocator and assignment containers. No gate, cap, event timing, polynomial coefficient or valid output changes.

Original compiler SHA256: `a6894f6c3da3ee8c3bce24875d34bd9df4b2d77546f162bf63a5648d618cebef`.
Patched compiler: `85dca2b8a53492a4193bd0da44bfaf228d14a00ddb1ab6d21927f40746306841`.
Patch: `79f86b626d7d067117ad010b63bcf2c7f3113b7caa43ae15cc7f01051988c77d`.

Minor documentation inconsistency: article line196 says identical body literals are removed during validation, while the implementation and later article contract reject duplicates. This does not affect accepted catalogues or any theorem; the later contract describes actual behavior.

## Optional exact-scale loader defect and separate repair

Original `bellman_diophantine.py` accepts an integer `scale` in `Program.encode` but does not normalize it to Fraction before `scale/(1<<counter)`. For a one-state halt program, `encode(0,[1075],scale=1)` returns counter coordinate0.0, whereas the default or explicit `Fraction(1)` returns the correct nonzero value2^-1075. This affects an explicitly supplied optional scale; the default path used by every shipped compiled-game loader is safe. It does not invalidate the counter-map proof or the published numerical examples.

The separate `exact_convergence_integer_scale.patch` accepts only an exact integer or Fraction, converts it to Fraction before arithmetic, and retains the existing positive-scale requirement. Floats and Booleans are rejected. It is disjoint from the checker repair and leaves both earlier patch hashes unchanged. Original generator SHA256: `5a5b20f384afb64f9a408dcd7a86f1e9c27dabfb9fcf9401540d479512391397`. Patched generator: `5ac8bbee279140e68d591874a10a00221799c9c2f94d154b6396c966993cf706`. Patch: `27879a31d4b574d962a22044a09a005045d5f0a182f4786f891951d677254f25`.

The standalone portable `incoming_convergence_scale_checks_808b.py` exposes `verify(bellman_root, scale_patch)`. It compares original and repaired behavior, tests counters through4096 and 100-digit integer scales, checks nontrivial positive rational scales and native increment/decrement transitions, rejects invalid scales, privately replays the full author suite and compares all eight regenerated exports. The fresh scale-only replay passed54 exact encodings,54 integer/Fraction comparisons,12 invalid-scale rejections,24 native counter steps and the full26,077-assertion author suite; all eight exports and the normalized receipt remain unchanged. For composed repair validation, the root integration passes a private package with the independently pinned checker patch already applied: the scale helper pins the original generator and its own generator patch, and then runs the complete author suite in its private copy. This additional defect is recorded separately; the original four-finding helper remains frozen.

## Repair validation and useful arithmetic transfer

The portable repair checker applies each pinned patch with `--fuzz=0` to exact original source in a temporary directory. It passes 146 malformed/adversarial rejection cases, 27 general rational Bellman scaling cases, all three delivered Bellman certificates, deep input/export snapshot tests, three complete patched author/checker suites, 12 byte-identical exports and two unchanged normalized author receipts. Namespace cleanup is explicit. These are proposed source repairs delivered as patches, not alterations to the historical ZIPs.

A concrete local simplification is worth implementing separately. In each private min gate, set `z=x−a`, delete its first affine row and retain `y−x+a−b=0` plus `ab=0`; for max use `z=x+a` and `x+a−y−b=0`. Natural slacks and complementarity reconstruct the true nonnegative output for nonnegative inputs. Since emitted gates are ordered, this gives a unique natural lift through the complete gate DAG. In each typed mux, set `f=t+a`, remove the first row and retain `M−t−a−h=0` and its two products. The actual compiler never uses z or f as a complementarity-product factor, so these substitutions retain quadratic degree and global orthant nonnegativity.

If implemented with exact guarded source substitution, this would remove G+D witnesses and G+D affine-square rows from the general compiler, giving `W'=m(2q+3)+2D+2G+R`; the Horn allocation becomes `m+2G+R`. This is presently a proved local transfer proposal, not a shipped rewritten compiler. Affine expressions may grow on substitution, so no arithmetic-operation saving is claimed from witness deletion alone. The Bellman compiler's state outputs have additional shared downstream uses and require their own full source/operation analysis.

The [batch replay](incoming_substrate_review_808b53ed8.py) runs both source reviews, both main repairs and the composed Bellman checker/scale repair. The committed receipt records them under `independent.convergence`, `independent.convergence_repairs` and `independent.convergence_scale`.
