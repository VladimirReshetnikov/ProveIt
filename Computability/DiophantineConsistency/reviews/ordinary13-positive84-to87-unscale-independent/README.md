# Independent review: positive 84↔87/36 q³ unscaling

This source/math review covers
`research/ordinary13-positive84-to87-unscale-model-audit/`. The author's
receipt reproduces. The independent checker pins the exact graph and source
inputs, verifies the full row delta and three non-first residual dependency
sets, proves the root/residual scaling and cube Bézout identities with exact
sparse polynomials, and checks bounded tau-margin controls. Run
`python3 -I -S -B check.py | cmp - receipt.json` from this directory. This
is not a Lean/model-provider or endpoint proof.

Write `h=q³`, `Y=h*s`, `b=J*beta`, and let B be the signed first carrier.
For signed `r_old=r_new−s`, the exact graph root rows yield

```
Z_old = h*b*(ell+k+r_old−k*B) + Y*b − h*B = h*Z_new,
A_old = h²*A_new.
```

Here `A` denotes the first residual, so its square in the four-square output
scales by **h⁴=q¹²**; the total outputs are not pointwise equal. The other
three residuals have identical rows and do not depend on r. At a zero,
recovering their individual vanishing and canceling the positive h² scale
needs the intended ordered integral-domain model facts and actual field/cast
bindings, not just polynomial substitution.

For 87→84, the proposed signed-quotient interface has exactly the usable
shape: `z=h*b*t+Y*b−h*B`, `z²=(h*b)²*n`, positive natural Y and
`h=(1+b)³`. Square divisibility supplies signed `h∣z`, so the displayed
root gives `h∣Y*b`. The exact ring identity
`(1+b)³−b*(b²+3b+3)=1` cancels b and gives signed `h∣Y` without a hidden
coprimality premise. The cited signed-to-natural reflection then supplies
positive natural s with `Y=h*s`; r_new=r_old+s is positive. This is the
conditional source interface `positive_quotient_of_signed_norm`, not an
already-proved fact about the selected 87 graph.

For 84→87, direct r_old=r_new−s need not be positive. After separately
extracting a positive represented B=b*t and the same-model first root
magnitude tau, the stronger margin `tau>ell+s` permits
`r_old=k*(B−1)+t+(tau−(ell+s))>0`. The associated new-graph coordinate is
`r_old+s=k*(B−1)+t+(tau−ell)`, so the exact first root is `+b*tau` and the
old scaled root is `+h*b*tau`. The other residuals are independent of r.
This is a witness replacement, not a same-coordinate inverse.

The cited `P73Converse.tau_gt` has the exact fact-level inputs
`tau²=1+ell*(ell+k)`, tau≥0, `3s≤k`, and `0≤s≤ell`, and concludes the
strict margin. Its proof is private and cannot simply be imported as a public
lemma. Given model facts `m=XY²`, `ell=m*k`, positive X/Y/s, `Y=q³*s`, and
`k≥8m+4`, one has `m≥Y≥s`, hence both `3s≤k` and `s≤ell`; those casts,
large-k hypotheses and actual graph norms are still to be established. The
fact-level control `m=1,k=2,ell=2,s=1,tau=3` satisfies the norm and s≤ell
but has `tau=ell+s` when `3s≤k` is omitted. It is not a selected-graph zero.

No mathematical scale, sign or interface mismatch was found in the inspected
cuts. The q³ extraction, B positivity/divisibility, natural tau and strict
margin, root branch, exact graph maps, source/provider/axiom closure, compact
port provenance and physical PDF/iPRA endpoint all remain unelaborated. The
isolated r_new=1,s=2 predecessor control is not a graph-zero example.
