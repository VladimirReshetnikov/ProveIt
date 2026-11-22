# Independent mathematical review of the measure chapter

## Scope and verdict

Reviewed `work/measure.tex`, including the version in which (M19) is used to derive a global energy cap and L1 domination is explicitly defined through positive-part norm zero. This is an independent mathematical review of the written arguments, not a claim of formal verification.

**Verdict:** no blocking mathematical error found after the domination-interface clarification was incorporated. The numerical constants and the principal finite-to-name constructions check out. The conclusions remain conditional on exactly the named computational data; the chapter does not claim arbitrary sigma-algebras, pointwise sections, or an unqualified Radon–Nikodym theorem.

## 1. Dyadic completion and effective Boolean unions

- The convention `||a_q-a_p||1 ≤ 2^(-p)` for `q≥p` is sufficient for the stated completed norms and integrals. Conversion from the symmetric regular-name convention by one index shift is correct.
- In the effective-union constructor, each finite approximation contributes at most `2^(-p-2)`, and each prefix-to-common-prefix comparison contributes at most the same error. For `p≤q`, the total is at most `2^(-p-1)+2^(-q-1)≤2^(-p)`.
- `T` need not be increasing or tend to infinity. The comparison to the maximum of the two requested prefix lengths uses (M3) separately at the two requested precisions and is valid. If `T` stays bounded, the tail condition forces omitted sets to have vanishing measure, which is consistent with the claimed least upper bound.
- Pairwise disjointness modulo zero is adequate for finite additivity; the supplied tail estimate then gives the scalar sum rate. This is effective countable additivity on a specified family, not unrestricted countable closure.
- Variable-length batch production is explicitly accounted for. Individual termination of each input name is not silently promoted to a uniform batch.

## 2. Fubini and conditional averaging

- The partial-average contraction is the finite weighted triangle inequality. Extension on rapid names is immediate with no shift.
- The Fubini identity is a finite equality of rectangular sums before passing to names. It does not require integrability of every pointwise section.
- The tower identity uses nested dyadic partitions and is correct.
- The convergence estimate `||E_n f-f||1 ≤ 2||f-a_(p+1)||1≤2^(-p)` is valid when `n` is at least the level of the approximating step. Thus a strong name really does provide the claimed rate.

## 3. Clipping, Vitali, and uniform integrability

- The old threshold inequality (M11) is correctly identified as false by `x=2,y=-1,K=1`.
- The replacement (M10) is correct for `K≥1`: the clipped difference is bounded by `min(|x-y|,2K)≤2K min(1,|x-y|)`.
- In (M13), `K≤2^h` makes the metric term at most `2^(-p-2)`. Adding the two tails gives `(3/4)2^(-p)`.
- Running maxima in the selected subsequence ensure both indices lie beyond the same original threshold. No monotonicity of `N` or `U` is assumed.
- The extension from step sequences to uniformly presented L1 names has enough guard bits: the sum of the two approximation errors and the selected subsequence discrepancy is strictly below `2^(-p)`.
- The moment bound `4K(u-K)^+≤u²` is valid and has the sharp scalar coefficient used. The proposed `U(p)` is therefore sufficient, with spare precision.
- A clarification requested in review has been incorporated: domination is defined by `||(|f|-G)^+||1=0`. The finite inequality `t_K(x)≤(|x|-y)^+ + t_K(y)` transfers the tail estimate to names without choosing pointwise representatives.
- The blueprint correctly types amplitude cutoffs as rational values, so the rational maximum in (M16) is compatible with the bounded logarithm search.

## 4. Density construction and extension of the measure

- Coherence of masses yields the coarse-cell average identity. The cross term `I(d_m d_n)=H_n` is correct, so `Q(d_m-d_n)=H_m-H_n` follows by expansion.
- The monotone schedule `r(p)=max(p,max_(j≤p)R(j))` gives both rapidness and eventual refinement of every fixed dyadic set.
- Uniqueness follows from equality of all dyadic cell integrals and the already proved conditional-average convergence theorem. It does not need pointwise differentiation or a theorem about arbitrary measurable sets.
- (M19) implies a uniform cap: levels below `R(0)` are bounded by monotonicity, while later levels are within one unit of `H_(R(0))`. Therefore `C=H_(R(0))+1` is valid.
- The continuity estimate for the induced measure is the finite Cauchy–Schwarz inequality applied to `d_n(1_A-1_B)` at a common level. Its square root can be eliminated by squaring nonnegative rational quantities.
- Extending the scalar map `A ↦ ν(A)` along Boolean names is legitimate. First define the density integral on dyadic sets using the L1 contraction, then extend that scalar map by the same continuity bound. This does not assume unrestricted multiplication on L1.
- An explicit schedule is available: if `J≤2^h`, a rapid Boolean name `A_p` gives a rapid scalar name `ν(A_(2p+2h))`. Likewise a lambda-tail cutoff `T` yields a nu-tail cutoff `p ↦ T(2p+2h)`. This schedule was suggested to the author as a useful expositional addition; the original continuity argument was already sufficient mathematically.
- The local sibling estimate gives the energy increment `(L²/4)4^(-n)`. The finite geometric tail is `(L²/3)4^(-n)`, and `R(p)=p+h` with `L≤2^h` is valid.
- The explicit affine-density example has the stated energy `28/27-4^(-n)/27` and sibling difference `(1/3)2^(-n)`.

## 5. Metastability and the no-rate obstruction

- The sequence `t_(j+1)=max(t_j,g(t_j))` is allowed to stall. A stalled interval immediately satisfies the target, so no strict progress assumption is missing.
- With `B=C0*4^p+1`, all `B` energy increments being larger than `4^(-p)` would exceed the total available energy. The finite search bound is correct.
- For two levels in the chosen interval, monotonicity bounds their energy difference by the endpoint increment; the L1 estimate then follows from (M18).
- The challenge function is fixed before primitive recursion, so the argument does not introduce a universal evaluator for all PR programs.
- In the no-rate construction, a machine first halting at time `t` introduces a Rademacher perturbation at level `t+1`. It has mean zero on every coarser cell, so the dyadic masses remain coherent. The densities are nonnegative, total mass is one, energy is either one or `5/4`, and the jump has L1 size `1/2`.
- A purported uniform Cauchy rate at tolerance `1/4` rules out any halt at time `t≥N`; simulating the first `N` time positions therefore decides halting. The time convention is internally consistent with the chapter's condition `t<n`.
- The obstruction is correctly stated as metatheoretic nonexistence of a uniform computable operation. It is not overstated as a specific independence theorem in iPRA.

## Remaining formal work

The review validates the written mathematical reductions. The finite rational invariants still need the stated coding, proof construction, and `Prf PRAAx` derivations before the universal analytic results may be called kernel-checked object-theory theorems. The chapter and blueprint retain that distinction.
