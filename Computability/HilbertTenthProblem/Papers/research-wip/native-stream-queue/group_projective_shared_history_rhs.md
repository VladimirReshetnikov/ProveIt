# Sharing the history right-hand sides saves one multiplication

The four signed history equations contain two common right-hand sides.
The odd one can reuse the even one and the controller's existing `P+1`
register. This removes **one multiplication** without changing any
retained register value, comparison, witness or final polynomial.

The rewrite applies to all three current variants: the four-field and
six-field [factored-index compilers](group_projective_factored_native_index.md),
and the [shifted-X compiler](group_projective_shifted_X_quotient.md).
The last becomes **256 certificate / 279 polynomial operations**, with
eight equations, 42 positive witnesses and exact degree 4298 for the
illustrative ten-letter table with both options enabled.

These remain parameterized fixed-table results. They do not instantiate
the universal numerical alphabet or replace the separate numerical
universal bounds of 75 certificate / 88 polynomial operations.

## 1. Exact identity and literal source saving

The parent computes

    c0=D-1, d0=c0+u,
    UP=c0*P, right_even=UP-D,
    VP=D*P, right_odd=VP-d0.

The controller already computes `lane_factor0=P+1` in every variant,
including the smallest padded alphabet. Hence

    right_odd = D*P-(D-1+u)
              = ((D-1)*P-D)+(P+1)-u
              = right_even+lane_factor0-u.                    (1)

Delete `d0` and `VP`, and replace the old `right_odd` subtraction by
one addition and one subtraction. The removed fragment uses `1M+2A`;
the replacement uses `2A`. Every other gate, including `c0`, `UP`,
`right_even`, and the already paid `P+1`, remains unchanged.

The [source](group_projective_shared_history_rhs.py) audits the exact
parent gates and checks that both deleted registers have just one
consumer, the replaced `right_odd` gate. Neither deleted register occurs
in a retained comparison. It orders the replacement topologically, so
reusing a controller register creates no forward-reference assumption.
Both supplied `P` and computed `P=(B-1)J+1` are handled explicitly.

Identity (1) holds over all integer assignments. Every retained register,
residual and complete final polynomial is therefore identical to its
parent. In particular, the positive zero sets agree on exactly the same
witness vectors. The parent's exact degree proofs apply unchanged.

## 2. Complete compiler ledgers

Use the preceding fixed-table notation and hypotheses:

    C=3m+3h+p+185+f_flow-3min(h,3)-epsilon,
    L=m+18 if epsilon=0, L=2m+10 if epsilon=1,
    nu=1+chi.

Here `epsilon` chooses controller-mask reuse and `chi` chooses computed
length. The source keeps the inherited `p` metadata for the physical
port arithmetic; the new saving is the separate `-1M` above.

| Variant | Certificate | Equations | Positive witnesses | Polynomial | Exact degree |
|---|---:|---:|---:|---:|---:|
|Four-field, full SOS|C-2|12-chi|m+30-chi|C+33-3chi|22nu L+54|
|Six-field, outer product|C-2|10-chi|m+28-chi|C+27-3chi|nu(27L+m+15)+46|
|Shifted-X, outer product|C-2|9-chi|m+27-chi|C+24-3chi|nu(44L+9m+135)+44|

For the illustrative ten-letter table, the shifted-X choices are:

| Mask reuse | Computed P | Certificate / polynomial | Equations / positive witnesses | Exact degree |
|---|---|---:|---:|---:|
|Yes|Yes|256 / 279|8 / 42|4298|
|No|Yes|257 / 280|8 / 42|3594|
|Yes|No|256 / 282|9 / 43|2171|
|No|No|257 / 283|9 / 43|1819|

The six-field supplied-P alternatives now give 285 operations at degree
1211 or 286 at degree 995, each with 44 witnesses. The four-field
no-mask supplied-P alternative gives 292 operations at degree 802 with
46 witnesses. No optimality claim is made among all possible rewrites.

## 3. Verification

The [receipt](group_projective_shared_history_rhs.json) contains thirty
complete option ledgers and one complete ten-letter certificate plus
its finalizer. It verifies the symbolic identity, deleted-consumer
sets, exact multiplication/addition counts and unchanged witness and
comparison lists.

It also evaluates every surviving register, every residual and the
entire final polynomial on 1,920 complete-source assignments, including
480 signed assignments, against the actual parent sources. These finite
checks supplement the polynomial identity and source audit; they do
not substitute for the parametric proof. Degrees are inherited by
identity of the complete output polynomials, not estimated from samples.

Run the checker normally to compare with its deterministic receipt, or
with `--write` to regenerate it.

Independent proof/source review and a fresh default replay passed with
no findings. Additional signed audits checked the direct history formulas
and complete polynomial identities, including two different affine input
loaders.
