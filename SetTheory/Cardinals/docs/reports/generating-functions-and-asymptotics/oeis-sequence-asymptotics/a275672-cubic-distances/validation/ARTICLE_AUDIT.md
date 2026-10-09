# Independent mathematical audit of the draft and finite bounds

Audited files:

* `../a275672.tex`
* `../src/finite_bounds.py`

The article's result-input files and the C++ search runs were outside this mathematical audit. A separate source audit is included in `SEARCH_AUDIT.md`. The reviewed article and programs were not edited during either audit.

## Overall conclusion

No substantive logical error was found in the elementary equal-norm energy proof, alteration lower bound, analytic Gaussian certificate, verified Gaussian certificate, finite geometric-series bounds, or structural/Sidon claims.

A formal clarification identified in the optional geometric appendix has been applied in the final manuscript. The original draft suppressed `o(1)` errors in the variance and tail-integration inequalities for finite empirical measures. The corrected argument takes a subsequence with `m/N -> c > 0`, treats `c=0` separately, retains the vanishing errors, and then passes to the limit. The stated uniform cumulative-distribution error justifies this passage.

## Elementary O(N^4) equal-norm count

The proof maps `(u,v)` injectively to `(a,b)=(u-v,u+v)` with `a.b=0`; ignoring parity is a valid upper bound. For a nonzero primitive direction `a_0` of sup norm `r`, choose the third coordinate with magnitude `r` and put `h=gcd((a_0)_2,r)`.

Primitivity gives `gcd((a_0)_1,h)=1`. The congruence modulo `r` forces `h|b_1`, after which `b_2` has exactly one residue class modulo `r/h`; `b_3` is unique if it lies in range. Therefore the bound

`(4N/h+1)(4Nh/r+1) <= 16N^2/r+8N+1`

is valid. The cases with zero coordinates are included: if the second coefficient vanishes, `h=r`; if both first two coefficients vanish, primitivity forces `r=1`, and the congruence is correctly vacuous.

The shell count `24r^2+2` bounds all primitive directions, and there are at most `2N/r` positive integer multiples. The dominant terms in the sum are `O(N^3)` per shell and `O(N^2 r)` per shell; summing to `2N` gives `O(N^4)`. The residual `N^3 sum r^-2` and `N^2 sum r^-1` terms are smaller. Hence `T=O(n^7)`, `Q=O(n^10)` and the fully elementary `Omega(n^(2/3))` alteration proof are sound.

## Analytic certificate

The masses, support potential equalities, coefficient ratios, and formula for `C_6` were checked. In particular, the three first ratios are correctly

* `r_1=144 alpha/245`,
* `r_2=96 alpha^2/245`,
* `r_3=192 alpha^3/1225`.

The one-sign-change comparison with `t^4 F(1)` is valid by absolute convergence and the established signs.

The proposed rational logarithm bracket was checked exactly. For `J=10`, its lower and upper rational endpoints are

`8489584743055122319240 / 4738532127454800918243`

and

`79243465812347889693115 / 44226299856244808570268`.

They satisfy `179/100 < lower < upper < 9/5` by integer comparisons.

## Finite Gaussian upper-bound implementation

The interval routine encloses `exp(-x)` correctly: it reduces to `x/128<=1/2`, uses odd/even alternating Taylor brackets, rounds every term outward, and performs seven positive directed squarings.

For the first geometric series, `q/(1-q)` increases with `q`, so the upper endpoint is correctly used. For each subtracted progression, using a lower numerator and a lower exponential in the denominator yields a lower bound for the entire positive ratio; subtracting it gives an upper bound for the remaining sum. Omitting later subtracted terms is also in the safe direction.

The loop condition `7 delta 4^a <=56` ensures that the denominator exponent `8 delta 4^a` is at most64, within the exponential routine's declared range. The quadratic predicate is true on an initial interval of the nonnegative integers and false thereafter, so the binary search is valid despite the quadratic's initial decreasing segment.

The fixed `10^60` arithmetic scale could eventually be insufficient for astronomically huge side lengths where the upper exponential endpoint rounds to1; the routine then raises an error rather than producing a false bound. This does not affect any reported range. If the implementation is later advertised for unrestricted enormous integer input, adaptive precision or an explicit precision check would be appropriate.

## Independent finite checks performed

The bit-polynomial palette implementation was checked against explicit coordinate-triple enumeration for every `n=0,...,25`. Palette cardinalities and odd-distance counts agreed exactly.

The reported larger-size bound table was reproduced exactly:

| n | distance count | palette | parity | Gaussian |
|---:|---:|---:|---:|---:|
| 50 | 4606 | 96 | 96 | 101 |
| 100 | 19798 | 199 | 199 | 193 |
| 200 | 83752 | 409 | 409 | 378 |
| 500 | 554119 | 1053 | 1052 | 932 |
| 1000 | 2287097 | 2139 | 2138 | 1857 |

Independent combinatorial enumeration at `n=7` verified:

* 66 possible squared distances, of which 30 are odd.
* The 55th squared distance is68.
* Modulo-four capacities through70 are `(14,17,17,8)`.
* All 31,824 weak compositions of 11 into 8 coordinate-parity classes were checked; none satisfies those capacities.
* There are 810 unordered grid edges of squared length at least68.
* These edges have 31 orbits under the 48 cube isometries.

These enumerations were written independently in Python, not extracted from the C++ solver.

## Structural claims

The additive Sidon terminology is correct: equality of two nonzero ordered differences would give repeated norms, and the only allowable unordered-pair identification then preserves the ordered difference. Conversely `{0,e_1,e_2}` is already an additive Sidon set with repeated Euclidean lengths, so the distinction is real.

The eventual-strict-monotonicity implication `a_n >= n-O(1)` and the sublinear-growth implication of `N-o(N)` plateaus among the first `N` transitions are both correct. Neither decides which behavior occurs for the cubic sequence.

