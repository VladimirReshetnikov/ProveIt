# Independent review: 13-natural-input, 89-operation graph

The [candidate](../../research/ordinary13-natural-unit-product89/README.md) has the stated external zero-existence relation to the reviewed 13-positive, 80-operation parent when `beta>0`. The graph, root-switch argument and degree claim are sound conditional on the cited parent factor-exclusion and degree certificates. This is not a Lean or iPRA theorem, physical PDF binding, fresh provider replay, or minimality claim.

The independent receipt checks all changed and common graph rows, the 13 inputs and four ports, topology and liveness, and the literal first-factor and root-dependency structure. The graph is exactly the parent with `f`, `r`, `y` unshifted and the other positive coordinates shifted by one, using the documented `k`/`r0` cancellation. It confirms that `r` occurs only in `g31` and cannot affect `F1`, `Fa`, or `Fs`. It independently reauthenticates the P72 port bytes against the pinned P115 hashes and computes the degree-99 diagonal ray modulo 1,000,000,007. The degree upper bound is inherited from the separately reviewed parent; this receipt does not independently rederive that bound.

For the unbounded `r=0` case, the parent's all-integer unit-factor exclusions give `Z²=b²*(1+ell*(ell+k))`, with `b>0`, `ell>0`, and `k>=2`. If `B<=0`, the defining equation gives `Z>=b*(ell+k)`, while `(ell+k)²>1+ell*(ell+k)`, a contradiction. Thus `B>0`. Integer divisibility of squares gives `b | Z`; then `Z=b*(ell+k-k*B)-B` gives `b | B`. Put `t=B/b>=1` and `tau=|Z|/b`. The norm yields `ell<tau<ell+k`. If `Z>=0`, the defining equation instead gives `tau=ell+k-k*B-t<=ell-1`, a contradiction. Hence `Z<0`, and replacing `r=0` by `2*tau>0` changes `Z` to `-Z` while keeping all other factors fixed. This yields a positive-parent zero, even though the original natural zero need not already have positive `r`. The finite abstract example in the receipt illustrates only the algebra; it is not asserted to satisfy all graph constraints.

The source also correctly rules out `f=0` using the strong unit equation and `y=0` using divisibility by `Delta>1`; the remaining coordinates are positive by their input shifts. No argument here establishes the inherited compact44 endpoint or internalizes the root switch in iPRA.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary13-natural-unit-product89-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary13-natural-unit-product89-independent/result.json
```
