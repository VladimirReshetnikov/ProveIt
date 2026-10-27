# Cached corollary for degree at most s^0.51

**Result.** Under the same normalized ring, tensor-description, entry-oracle and immutable creation-precision premises as the main theorem, strengthen the root maximum-degree promise to `ceil(s^(51/100))`. Then the four-plan r=13 rectangular evaluator gives

`T,S ≤ poly(s+L) 2^{(C+o(1)) s/sqrt(ceil(log2 s))}`,

where

`C=(π/ln2) sqrt(27980397750833/2732730000000)`

and

`14.502837849049 < C <14.502837849050`.

Thus **14.503** is a safe eventual coefficient for both time and space. Space is subexponential, not polynomial. This complements the polynomial-space degree≤s^.51 branch; it does not replace the stronger degree≤s^(1/12) cached specialization. Every normalized family of degree `O(s^(1/2) polylog s)` eventually satisfies this degree premise, but numerical SAT-variable constants still require the encoder's wire-count analysis. No new SAT order or full SAT implementation is claimed.

## Fixed schedule and packing proof

Use the already certified four-plan r=13 menu, whose local squared time/space coefficient is

`β²=27980397750833/82810000000000`.

The paid singleton-entry coefficient is `α=sqrt(24)/13` and child wire ratio is `ρ=2/13`. Let `λ=ceil(log2 s)`, `B=ceil(6log2 λ)`, and stop at `H=ceil(s/λ^(2/3))`. Set

`f0=33/500`, `A=119/1000`, `θ=24/125`,

`f1=(A−f0)(1−θ)=5353/125000`,

`f_d=f1 θ^(d−1)` for `d≥1`,

`u_d=floor(f_d λ)`, `a_d=Σ_(j≤d)(u_j+B)`.

All calls use arity13. The total leading retained range is exactly `f0+f1/(1−θ)=A`.

Three exact integer inequalities provide strict fixed packing slack:

1. `13^66<2^245`, equivalent to `(51/100)+2f0 log2 13<1` at the root.
2. `13^119<2^490`, equivalent to `(51/100)+A log2 13<1` for the retained high-degree side later.
3. `338^119<2^1000`, equivalent to `A(1+2log2 13)<1`, covering both fresh-side and packet-rounding terms since `338=2·13²`.

The fresh packet degree is at most `s^(A+o(1))`, with `A=.119<.51`; hence the retained-side degree invariant remains valid. These strict power gaps absorb buffers, polylogarithmic factors, and `s/M<λ^(2/3)` at every active call.

For the noncircular depth argument, provisionally consider active depths up to `(2/3)log_6 λ+O(1)`. Since `ρ<1/6<θ`, the smallest taper there is

`λ^{1+(2/3)ln(θ)/ln(6)+o(1)}`,

whose exponent exceeds1/3. Thus floors are uniformly negligible. Nearly lossless packing is valid throughout the provisional range and gives child ratio `ρ+o(1)<1/6`; an active path cannot exceed that depth. Relative padding error can be chosen `O(λ^-3)` plus a fixed negative power of s, so accumulated errors over `O(log λ)` levels are `o(1)`.

At retained valuations, `D≥2^(a_(d−1)+B+1)`. Inherited precision `O(sλ²2^a_(d−1))` is at most an `O(λ^(11/3)2^-B)=o(1)` fraction of `MD/u_d`. This preserves the inherited precision-six and entropy estimates. Leaves cost `2^{O(s/λ^(2/3))}`; new packet entries cost `exp(s^(.119+o(1)))`; even the unchanged generic original-entry allowance `poly(s+L)2^{O(s^.9)}` remains lower order. No stronger original-entry assumption is needed. All precision/extension/description parameters stay polynomial. The immutable creation-time representative convention is unchanged.

## Fully paid recurrence and constants

Let `κ=πsqrt(2)/ln2` and

`K0*=κ/sqrt(f0)`, `K1*=κρ/sqrt(f1)`, `γ=ρ/sqrt(θ)`.

All later K coefficients decrease geometrically by γ. The unchanged paid recurrence gives time coefficient

`max{βK0*, αK0*+K1*max[β,α/(1−γ)]}`.

Exact rational intervals establish

- `.351104203528 < γ <.351104203529`;
- `.580747444909 < α/(1−γ) <.580747444910`;
- `.581280226306 < β <.581280226307`.

Therefore the tail's local aggregation term dominates its paid infinite cache series. The descendant route satisfies

`12.172129729345 < αK0*+βK1* <12.172129729346`,

strictly below the root route `βK0*=C`. Also `K1*<K0*`, so the root is the largest local table. Ancestor tables add sizes instead of exponents, giving the same coefficient C in space. Per-level polynomial overhead contributes only `O(λ log λ)` exponent bits. The complete statement follows.

## Evidence

- `matrix_checks/verify_degree_051_cached.py`
- `matrix_checks/verified_degree_051_cached.json`
- `matrix_checks/verified_degree_051_cached_optimized.json`

The checker uses the previously authored exact rational interval tools, checks all three integer gates and the complete paid recurrence, verifies the closed radical, and includes two negative controls. Normal and optimized outputs are byte-identical. It imports only our own code and executes no incoming program. The local four-plan certificate remains the dependency proved and independently checked in `four_plan_portfolio_new.md`; this corollary adds no new menu search or optimization.
