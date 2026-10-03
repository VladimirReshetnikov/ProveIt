# Exact sharing across the three Tree beta queries

The three-query arithmetic can be reduced to **50=17M+33A** when its two active ports are already supplied, or **51=17M+34A** when `active=t3+t4` is computed and paid here. The matching separately guarded baselines cost 53 and 54 operations. Both complete sources use the same **twelve natural witnesses** and have exact degree **seven**. They are the same full polynomial as their respective baselines on every supplied tuple; the witness maps are the identity.

This is a local successor to the frozen [beta-membership interface](eager_tree_beta_membership_interface.md), not a new unbounded Tree compiler. The [source](eager_tree_beta_three_query_sharing.py) and [receipt](eager_tree_beta_three_query_sharing.json) authenticate that complete parent trio, read its literal 16/17-gate sources from the saved JSON, and execute no historical Python code. No original artifact is changed.

## Complete polynomial identity and payment

All three queries share the supplied natural sequence parameters `A,b`, current index `i`, and length `N`. Their evaluated targets are `D0,D1,D2`. Query `j` has independent natural witnesses `hj,kj,qj,sj`. Put

```
Jj = i+hj+2
rj0 = A-Dj-qj*(1+b*Jj)
rj1 = b*Jj-Dj-sj
rj2 = N-Jj-kj
Sj = rj0²+rj1²+rj2².
```

The parent natural theorem says `Sj=0` exactly when these witnesses certify an index strictly between `i` and `N` whose canonical beta remainder is `Dj`. An existential witness exists exactly for such suffix membership. The remainder and both index bounds remain present in every query.

The separately guarded baseline is

`active*S0 + active*S1 + t3*S2`.

The new source computes `I=i+2` once, then `Jj=I+hj`, and returns

`active*(S0+S1) + t3*S2`.

Every query residual remains the identical polynomial. The final change is distributivity, valid over every commutative ring; no equation or sign hypothesis is used. There is no supplied-coordinate shift, hidden restoration arithmetic, or altered zero tuple.

The complete count is:

| Component | M | A |
|---|---:|---:|
| Three complete ungated 16-gate atoms | 15 | 33 |
| Share `i+2` across all three | 0 | −2 |
| Form `S0+S1`, multiply by `active`, multiply `S2` by `t3`, add both | 2 | 2 |
| **Supplied-active complete output** | **17** | **33** |
| Optional actual `active=t3+t4` gate | 0 | 1 |

Three independent guarded 17-gate atoms plus the two final sum additions cost **53=18M+35A**. Paying their same `active=t3+t4` gate gives **54=18M+36A**. Thus each matched comparison saves exactly **1M+2A**, including the complete outer finalizer. Constants are charged when operated on. The prefix `i+2` is computed here, rather than renamed as a free supplied port.

There are twelve witnesses, not four shared across queries: every `h,k,q,s` tuple is private. A genuine membership choice in one slot cannot silently supply the bounds or quotient of another. `D0,D1,D2` are already evaluated scalar inputs to this local circuit. Their actual Tree target-code computations, the sequence code's relation to all row fields, and the bounded-universal compilation remain external and unpaid by these counts.

## Domains, degree, and interfaces

On natural assignments, each `Sj` is nonnegative. Hence the shared guarded polynomial is zero precisely when every query with positive active coefficient has zero `Sj`. In the Tree interface, the first two slots have common coefficient `t3+t4`, and the third has coefficient `t3`; the separate one-hot theorem makes these coefficients Boolean. The present algebraic identity does not need that Boolean restriction. An inactive slot, including an empty suffix, stays unrestricted and contributes zero.

In supplied-active mode, `active` and `t3` are independent natural inputs; their relation to Tree tags must be established by the caller. In computed-active mode the source explicitly computes `active=t3+t4`, charging one addition. Neither mode silently asserts this relation from input names. Signed/rational evaluation is used only to verify the all-value identity, not to extend the natural remainder theorem.

The complete degree-seven leading form in supplied-active mode is

`b²[active*q0²(i+h0)² + active*q1²(i+h1)² + t3*q2²(i+h2)²]`.

Computed-active mode substitutes `t3+t4` for `active`. These are nonzero polynomials, and all remaining terms have degree at most seven. Targets here are independent scalar ports; substituting higher-degree target circuits changes this local degree analysis and must be charged separately. No fixed-arity universal degree bound is claimed.

The public APIs are `canonical_parent(computed_active=False, *, root=None)`, `build`, `checked`, and `evaluate(packet, values, *, signed=False, root=None)`. The option and `signed` flag must be exact Booleans. Packets are checked against their complete canonical descriptor; assignments contain exactly all declared input/witness names, with exact natural integers by default or integers when `signed=True`. All three parent byte pins are checked on every reconstruction; fresh packet metadata and source lists are copied.

## Two unsafe fifteen-gate coordinate changes

The standalone 16-gate atom has not been improved. The receipt includes two concrete syntactic 15-gate rewrites only as counterexamples to dropping inverse inequalities.

1. Supplying `H=i+h` and replacing the two gates for `i+h+2` by `H+2` requires the inverse `h=H−i` to be natural. It is not forced by the other rows. The tuple

   `A=0,b=1,i=1,N=2,D=0,H=0,k=0,q=0,s=2`

   makes the new full polynomial zero, while the interval `i<j<N` is empty. The putative inverse has `h=−1`.

2. Supplying `S=D+s` and replacing `b*J−D−s` by `b*J−S` requires `s=S−D>=0`. Again it is not forced. The tuple

   `A=3,b=1,i=0,N=2,D=3,h=0,k=0,q=0,S=2`

   is a new full zero, but the sole possible index is one and `3 mod 3=0`, not three. Its putative inverse is `s=−1`.

Both false zeros are natural in their proposed new supplied coordinates. These are explicit failures of particular rewrites, not a lower-bound theorem for all coordinate changes. The safe three-query sharing avoids both changes and preserves every original coordinate and bound.

## Reproducibility and finite evidence

The writer expands and compares both entire source polynomials and all nine query residuals, recounts all gates and checks liveness and exact degree. It includes sixty full evaluations (24 signed and twelve rational), 24 natural identity-map zeros including inactive empty ranges, both exact counterexamples above, 39 rejected calls including nine warm-pin failures, seven mutable-packet copy checks, and optimized-Python rejection. Finite tests supplement the exact identities and natural-domain proof; they are not an unbounded Tree compilation.

The authenticated parent pins are:

| File | SHA256 |
|---|---|
| `eager_tree_beta_membership_interface.py` | `bdb27b56b8701a1e392e799e742d135a4c0f107abc987982c5eb59efe947be34` |
| `eager_tree_beta_membership_interface.json` | `de8da8729d5167aa1196d374d4603dec865a9b6ae4529747afc632576dd83f7b` |
| `eager_tree_beta_membership_interface.md` | `b7f3ef7c12f0ae0ff14cd49ec57802b06d6842bd5b30bc044397d02866a115e3` |

Standard-library replay:

```sh
python eager_tree_beta_three_query_sharing.py --root /path/to/parent-trio \
  --expect eager_tree_beta_three_query_sharing.json
```

The default root is the script's directory. `--output FILE` writes a deterministic receipt; saved comparison is recursively type-exact. The two complete baseline and successor circuits and expanded polynomials are in the receipt. No repository file or Git state is changed, and no general optimality claim is made.
