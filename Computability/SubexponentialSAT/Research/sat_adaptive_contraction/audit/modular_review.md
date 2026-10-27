# Independent review of the modular joint-Cauchy kernel

Reviewed frozen implementation: `practical_work/modular_cauchy.py`, together with its two rational controls, verifier, benchmark driver and final benchmark results. No production file was modified by this review.

## Correctness assessment

No algebraic or precision error was found. The key safety property is that exact powers of two are tracked as ordinary integer exponents and **only unit parts** are reduced modulo `2^p`.

For each slot x and mode b, the implementation maintains the products

`P_b(x)=product_{h<b}(x-s_h)/(T+x-s_h)` and
`Q_b(x)=product_{h<b}(s_h-x)/(T+s_h-x)`

as valuation/unit pairs. The known valuation of each crossing denominator is removed before its inverse is formed. The residual exponent after division by the factorial normalization is nonnegative, exactly as proved for the full-orientation basis. No already rounded nonunit residue is divided by two. For b>x's slot index, the exact feature is zero and the implementation leaves the initialized zero entry in place. At the diagonal b=j, no future nonzero feature exists, so skipping the zero-product update is correct.

The common factor `Gamma(T)/T` is evaluated by symbolically cancelling T first. Each scalar denominator `-q` contributes a separately recorded power of two and an invertible odd part. If a numerator is zero, the whole prefactor is zero. This handles zero and nonunit zeta inputs correctly; it does not incorrectly assume the node perturbation is a unit.

For `(Z/2^p)[U]/(U^2+U+1)`, the implementation's conjugate and norm are correct:

`(a+bU)^(-1)=((a-b)-bU)/(a^2-ab+b^2)`.

The norm is odd precisely when at least one coordinate is odd. The batch-inversion routine therefore uses valid unit inversions. Its scalar prefactor still performs one additional inverse. The final production counters report these separately.

## Independent additional check

`check_modular_independent.py` uses a different oracle from the production recurrence: it evaluates the original cancelled polynomial

`product_{q in [-L,L), q != y-x}(T-q) / C'(0)`

modulo `2^(p+v2(C'(0)))`, inverts the odd part of the scalar denominator, and removes its known power of two. This neither calls the modular prefactor nor uses the feature recurrence. Its independent multiplication is written directly in integer coordinates.

Both normal Python and `python -O` passed with the same digest:

`cc7ac2063b4bc99dd57e03c01e41161b4a1bee014219af79b13fab9d5e3f41c8`.

Coverage: 63 deterministic fixtures, packet half-size through 128, precision choices through 129 bits, 493 reconstructed matrix entries, 493 checks of the public `direct_entry`, 27 complete `truncate=False` exact feature-table comparisons, and zero, nonunit, negative and large signed extension inputs. This supplements the author's much broader small-case exact checks. It is a local finite check, not a formal proof or SAT test.

## Complexity and scope

The algorithm uses `O(NB+L)` ring operations plus input normalization and unit inversion, where `N=L/2` and B is the retained mode count. Counting `O(NB)` alone would overlook the prefactor and denominator preparation when B is zero. It has only `O(L)` distinct crossing denominators; output tables cost `O(NB)` ring entries, or streamed columns use `O(L+B)` storage. Accumulated unit residues have p bits per coordinate. Raw input unit factors may initially have `O(a+bitlen(zeta))` bits before reduction; a bit-time claim must include that input normalization.

This implements the scalar unramified quadratic extension only. It does not implement arbitrary residue-field degree, the full truncated polynomial tensor ring, packet coefficient extraction, the recursion, or SAT preprocessing. The scalar coefficients can be used by those future layers, but those layers are not provided by this module.

## Benchmark assessment

The task measured is the finite-precision target/source feature tables. Both exact controls are timed through their final modular reduction, which is necessary to produce the same requested output. Every warmup and timed output is checked for exact equality outside the timed interval. Methods run in alternating order, with five measured repeats and medians reported. Raw samples are retained.

The first control is the unchanged archived full exact-rational implementation. It computes all modes, so its 51.15x--942.55x measured gaps include truncation and recurrence savings. The second control is substantially stronger: it adapts the already-existing exact recurrence, uses the same safe mode cutoff, and removes verification work from its timed section. Against that matched stronger control the final six-fixture medians range from **6.22x to 58.62x**. Those are the appropriate headline practical comparisons.

The separate-inversion modular control is sometimes faster than batch inversion in these small instances. Hence it is inaccurate to call the observed speedup a uniform batch-inversion gain. The main gain is bounded modular arithmetic with cached denominators and the same recurrence/cutoff; batching is an optional operation-count optimization whose constants vary at these sizes.

The measurements cover six local kernel cases on the recorded Python/Linux environment, not arbitrary inputs or end-to-end SAT. They establish actual performance improvements for these reproducible local instances and make no crossover prediction for the asymptotic contraction theorem.
