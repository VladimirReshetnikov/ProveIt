# Independent review of positive Markov guard savings

**PASS at the stated positive-integer, local-graph and fixed-duration scopes.**
The Boolean residual is redundant, the complete schedules have the claimed
costs, and both history families still recognize exactly `1 <= x <= T`.
No correction is requested. This does not establish a universal compiler or
a minimum arithmetic cost.

The frozen author artifacts reviewed are:

| File | SHA-256 |
|---|---|
| `markov_positive_guard_savings.md` | `901accac868c13967883c56ff5b5a949ef42fcfd82a470999f042272ead8dc15` |
| `markov_positive_guard_savings.py` | `122083814dedc5b565bddb94ff804a7821eb07340ff5aaafa932323e6eac258a` |
| `markov_positive_guard_savings.json` | `a2ee856af7bb2af3d09f38a28c3cd58e39e1dd902e9969732d3afe6890bf98d9` |

## Positive-domain proof and endpoint projection

For the direct graph put `u=C-1` and `t=B-2`. If `tu=0` and
`C'-u+t=0`, then `u=0` gives `C'=-t>0`; since the integer `t>=-1`,
this forces `t=-1`, hence `B=1` and `C=C'=1`. If `u` is nonzero,
then `t=0` and `C'=u>0`, giving precisely the decrement branch.
The converse substitutions are immediate. Thus the complete labelled graph,
including the selector, is preserved. The sum of real squares justifies
passing from polynomial zero to individual residual equations.

For raw coordinates, the zero guard is `t(X-H)=0`. If `X=H`, the
numerator equation forces `t<0`, so again `B=1`; using `qH'=H`
then gives `X'=H'`. Otherwise `B=2` and `X-H=qX'>0`. Dividing the
scale/numerator equations in the proof gives the asserted ratio decrement.
This argument needs no integral-ratio premise merely to force the selector,
but integral counter interpretation does. The two paid links provide it
locally. Every legal integer step extends with arbitrary positive `H'`,
then `H=qH'`, `X=HC`, `X'=H'C'`.

The three direct domain counterexamples and the unlinked ratio example
`(X,H,X',H',B)=(3q,2q,1,2,2)` check by substitution. They correctly
exclude nonpositive/rational selector extensions and unpaid integrality.
Also `H=qH'` prevents a positive integer successor with `H=1` when `q>=2`.

For a direct history, the omitted initial hat is a mathematical abbreviation
`C_0=x+1`; only its difference `u_0=x` is used. Every zero therefore
gives the unique legal path, and the endpoint forces `x<=T`. Conversely,
`C_j=max(x-j,0)+1` and the indicated selectors satisfy the source exactly
in that range. For raw histories, `u_0=H_0*x` binds the implicit initial
ratio to `x+1`. The affine recurrence propagates its integrality, and
positive numerators and denominators give positive integer hats. The
endpoint ratio is one. The witnesses `H_j=q^(T-j)H_T`, `X_j=H_j C_j`
prove completeness for any positive integer final scale. The source does
not evaluate a variable exponent or introduce an uncharged quotient.

## Identities, fully paid counts and degrees

Writing `b=(B-1)(B-2)`, the direct old polynomial equals the new one plus
`b^2`. In both history families the same statement holds with `sum b_j^2`
after the explicit initial substitutions. For the linked local graph,
put `L=X-HC` and `z_old=t(C-1)`. Then
`t(X-H)=H*z_old+t*L`, so the full difference is exactly

    (H^2-1)*z_old^2 + 2*H*t*L*z_old + t^2*L^2 - b^2.

All other old and new residuals coincide algebraically, up to their
irrelevant ordering in the sum. The stronger claim of all-value equality
is deliberately not made. The positive-zero equivalence follows from the
guard/link proofs, not from ignoring this correction. At `q=7` these bind
the actual prior arrays; `q=5` is the explicitly stated fixed-coefficient
substitution supported by the sine-lift interface.

| Complete source | Multiplications | Additions/subtractions | Positive witnesses | Exact degree |
|---|---:|---:|---:|---:|
| Direct local | 3 | 5 | 1 | 4 |
| Raw unlinked local | 7 | 7 | 1 | 4 |
| Raw linked local, endpoints C,C' | 11 | 11 | 5 | 4 |
| Direct history | 3T+1 | 6T | 2T | 4 |
| Raw history | 7T+2 | 8T | 3T+1 | 6 |

These include every fixed-coefficient multiplication, endpoint subtraction,
residual square and SOS join. Direct residual production is `1M+4A`
locally. The raw version is `4M+5A`; each of its two links adds `2M+2A`
including its square and join. For histories, the shared input difference
removes the old input addition and a cancelling subtraction. Counting the
displayed step templates gives the formulas for every fixed `T>=1`.
Against the old histories, each family saves `2T` multiplications and
`2T+2` additions, hence `4T+2` operations, with unchanged witnesses.

The direct quartic leader is supplied by a guard square (`B_0^2 x^2`
in the history). Local raw guards and links are at most quadratic and
include nonzero quadratic homogeneous parts, so their SOS has exact degree
four. The initial raw guard has square leader `B_0^2 H_0^2 x^2` with
coefficient one; all other residuals are at most quadratic. Thus raw
history degree six is exact. These are polynomial arguments, not merely
syntactic degree propagation.

The raw and direct local counts use different external ports until links
are added: fourteen is not comparable to twelve at the same integer-counter
endpoint interface; twenty-two is. Relative to the improved direct history,
the raw history still costs `6T+1` extra operations and `T+1` extra
witnesses. Changing the valid fixed mask coefficient from seven to five
reduces scale growth without changing this ledger. All these are specified
upper-bound schedules for a bounded counter language.

## Exact read and independent metadata scope

I read the entire author note (158 lines) and helper (291 lines) inertly.
The receipt binds five predecessor files. The old projective-counter note
(134 lines), its proof review (95), and the sine-lift note (192) were read
in full. The residue-affine comparison was read only at lines 1–66; its
external universality proof is not inherited or certified here. The old
JSON's local arrays were read at 697–787 and 1755–1945. Exact byte and
read-span hashes are in the independent JSON.

A newly authored metadata helper reconstructed all fourteen new literal
schedules, including all 368 rows, residual lists, outputs, external-port
and witness interfaces. It checked topology, complete liveness, arithmetic
ledgers, actual old local/history counts and the unchanged history port
sets. It **did not evaluate any saved source array**. The mathematical
identities and degree arguments above independently bind those templates.
The author's sparse coefficient tables and bounded numerical tests were
not independently recomputed or replayed; their checker implementation was
read. No supplied, frozen, author or predecessor program was executed or
imported. Only this fresh metadata code ran, before freeze, successfully
from `/`; no repository or Git mutation occurred.

Independent artifacts:

- `review_markov_positive_guard_savings_metadata.py`: SHA-256
  `069fa00f89ed7d704ce30480a74d14b7a9f3fca0c094aeeecb78c87f8deb1854`.
- `review_markov_positive_guard_savings.json`: SHA-256
  `3d3db0f9c47f286963489c387167d348e05adb90d2bb6280c344b52b00a4f564`.

The positive-domain guard elimination is accepted at this scope. Nothing
here transfers it without proof to other counter programs, a quantified
duration, the 84-operation universal construction, or an optimality claim.
