# Can precision peeling reset the cumulative packet scale?

## Status and existing result

The algebraic peeling identity is **already present**, with a complete creation-time precision-cap implementation, in:

`incoming_review/subexponential_sat_frontier_2026-10-26/subexponential_sat_frontier_2026-10-26/implementation.tex`, Section `Precision peeling for mode contributions`.

For a tuple of guaranteed target weight `W<P`, normalizing targeted packet factors gives exact contribution

`2^W product_g (Zbar_g mod 2^(P-W)) mod 2^P`.

The source-compatible implementation creates a new child network at residual precision `Q=P-W`, caps every retained representative at `Q`, and freezes those capped representatives. Caps flatten to their minimum. In cached evaluation an exact pair-weight array fixes total `W`, so an entire cached contraction can use the same residual ring. No new algebraic lemma is needed for these facts.

## The proposed additional step

At a parent call, `P` is of scale `M D/u`, with `D=2^(a-i)`. Standard partition heuristics put the typical residual precision near `D/sqrt(u)`, much smaller than `M D/u`. For these tuples, a child of wire size `Theta(M)` could plausibly reset its packet exponent rather than preserve the parent's full cumulative exponent.

This observation is valid for the common tuples but is not sufficient for the worst-case leading exponential certificate.

## The near-full-entropy residual tail

Let `lambda=log_2 s`, and fix any positive constant `B`. Consider all tuples with

`W <= P - P/lambda^B`,

or equivalently residual precision at least

`Q0=P/lambda^B`.

The old partition-counting certificate at this cutoff is

`S(P-Q0)=S(P) sqrt(1-lambda^(-B))=(1-o(1))S(P)`,

where `S(P)=Theta(sqrt((M/D)P))=Theta(M/sqrt(u))` is the leading logarithmic entropy. Thus the current proof still charges this exceptional set the **same leading exponent** as the full tuple family.

Meanwhile

`log_2 Q0 = log_2 P - B log_2 lambda`.

This only lowers the inherited precision exponent by `O(log log s)`, not by a positive fraction of `log s`. With `D=s^(A+o(1))`, the residual `Q0` has the same `s`-power as `P`. Therefore it requires the same leading cumulative packet exponent in the descendant precision-absorption argument.

This argument is a limitation of the existing upper-bound accounting. A counting upper bound alone is not an actual runtime lower bound. On a full regular linear-weight partition inventory, the usual saddle-point lower bound also gives the same leading entropy at `P-Q0`, but the existing source does not establish independent nonzero coefficients for every possible tensor input, so that observation must not be promoted to a tensor or SAT lower bound.

The same issue affects cached exact-weight arrays: arrays with total budget `(1-o(1))P` retain the same leading pair-index entropy coefficient, while residual precision `P/polylog(s)` retains the same polynomial power. Enumerating only polynomially many weight arrays does not make their near-maximal tables smaller at leading scale.

## Why a constant fractional split does not rescue the reset

A split at `Q=rho P` for fixed `rho>0` genuinely lowers the ancestor entropy coefficient by factor `sqrt(1-rho)`. But the low-residual branch still contains every `Q=P/polylog(s)` eventually. Such residuals have `rho=o(1)`, hence arbitrarily small leading entropy loss, while still preserving the full inherited precision power. A proof that only compares fixed-fraction residual bins misses exactly these bins.

Equivalently, suppose the fresh child scale must have `D_child` large enough that `Q` is absorbed into `M_child D_child/u_child`. Changing `Q` from `P` to `P/polylog(s)` changes the needed logarithm of `D_child` by only `O(log log s)`. It cannot make room for an additional retained range of order `log s`.

## Assessment

Precision peeling is exact and can substantially reduce polynomial arithmetic charges; the incoming packet already proves layer-cake and tilted-work bounds for that purpose. The typical-residual argument by itself does not yield a new leading coefficient or a new logarithmic order from resetting packet sizes. A successful extension needs another ingredient that handles the near-full-entropy, still-high-precision residual tail more collectively, or exploits cancellations/structural zero coefficients not represented by the current weight inventory.
