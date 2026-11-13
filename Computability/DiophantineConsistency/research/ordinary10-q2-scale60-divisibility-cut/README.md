# A 60-operation q²-scale candidate with an explicit divisibility cut

This literal candidate removes one multiplication from the 61-operation relaxed two-norm graph by changing its scale from `Y=q³s` to `Y=q²s′`. **Unconditional preservation of zero existence is open.** The candidate has ten natural witnesses, 60 live operations and the same four fixed natural ports. It retains the original positive `F` and `alpha` inputs; it is a separate proposal from the failed carrier-coordinate rewrite. No Con(ZFC), original-parent, Lean or iPRA equivalence is claimed.

## Exact maps and the missing implication

Write the predecessor's shifted natural input as `s=n_s+1` and the candidate's as `s′=n_s′+1`, with `q=1+beta*J≥1`. An arbitrary predecessor valuation maps to the candidate by

```text
s′ = q*s,   n_s′ = q*(n_s+1)-1,
```

leaving all ports and nine other witness inputs unchanged. This is natural. Both graphs then have the same `Y`, since `q²s′=q³s`; all later rows and the output agree exactly. Thus every 61-graph zero gives a 60-graph zero, regardless of any additional port inequalities.

Conversely, if a candidate valuation satisfies **`q | s′`**, let `s=s′/q` and `n_s=s-1`, retaining every other input. Because `q≥1` and `s′≥1`, the quotient is positive, and this is a natural predecessor valuation with identical output. Thus the 61 graph has a zero exactly when the 60 graph has a zero satisfying `q | s′`.

To claim an unrestricted one-operation reduction it remains to prove either (a) every candidate zero satisfies the divisibility condition, or (b) every candidate zero can be replaced by some candidate zero satisfying it. A nonlocal witness transformation would suffice for (b). Neither assertion is proved here, and divisibility must not be assumed merely because it held in the predecessor.

The cut is not a consequence of just the carrier and first norm residuals: with ports `(beta,K0,MC,MF)=(2,1,0,0)` and witnesses

```text
(n_J,n_F,n_alpha,n_w,n_s,n_h,n_tau,n_eta,n_zeta,n_gamma)
 = (1,0,0,2,0,3,973,0,1,0),
```

we have `q=3`, `s′=1`, `Y=9`, and both those residuals vanish, while the main residual is nonzero. This partial assignment therefore does not demonstrate a full counterexample to the divisibility cut; it shows that any proof needs additional information, for example from the main residual or a witness-changing construction.

## Reproduction and scope

The checker pins the predecessor JSON, checks the exact two-row source edit and all 60 live operations and 10 live witnesses, evaluates a bounded set of mapped valuations, and evaluates the displayed partial assignment. The quantified map proof is the elementary factorization above; finite tests are not a substitute for the missing zero-level implication.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary10-q2-scale60-divisibility-cut/check.py | cmp - research/ordinary10-q2-scale60-divisibility-cut/receipt.json
```

The argument is over ordinary natural inputs and integer-valued intermediate nodes; no nonstandard-model transport, provider audit, compilation, or Lean proof has been established.
