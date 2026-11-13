# Independent review: current 88/28 C-fold candidate

No concrete mismatch was found in the bounded source and mathematical review.
The candidate changes exactly `root_skew = k*Bt` to `root_skew = k*C` in the
pinned current 88/30 graph. It retains 13 inputs, four formal port positions,
all 88 live rows and the reported operation counts. The authored checker
reproduces. This is a conditional standard-integer comparison: **Cal remains
an explicit premise**, not a checked Lean, all-model, iPRA, or unconditional
endpoint theorem.

## Graph, degree and ports

The checker independently verifies topology, all-wire liveness, input order,
the exact one-row delta, and that the first-root coordinate `r` is used only
in the first-root branch. It decompresses and hashes the four pinned current
payloads, confirms `beta=2^(47*2011)-1` and the stated beta/K/MC/MF
inequalities, and evaluates 100 signed-port controls of the direct coordinate
map. These controls and byte checks do not prove Lean interpretation of the
payloads or a PDF binding.

For the upper degree bound, with fixed ports, `M*ell` has degree at most 8
and the difference `delta=Znew-M*ell` has degree at most 6. Expanding the
first residual cancels `(M*ell)^2`, giving degree at most 14; the three
unchanged residuals have degree at most 13, 13 and 10 by the cited parent
certificate. Thus the four-square output has degree at most 28. Independently
of the author's convolution implementation, this review evaluates the whole
literal graph at diagonal inputs 0 through 28 modulo 1,000,000,007. Its 28th
forward difference divided by 28! gives the nonzero coefficient 437565601.
Together these establish exact degree 28 for the pinned fixed payload tuple,
subject to the external parent degree certificate.

## Conditional candidate-to-parent map

At a positive candidate zero all four square residuals vanish. If `C<=0`,
then `Bt<0` using `K0>=0`, and the literal root satisfies
`Znew > M*(ell+k) > 0`. Its first norm would give a smaller positive
magnitude because `(ell+k)^2-[1+ell*(ell+k)]=ell*k+k^2-1>0`. Therefore
`C>0`. Square divisibility and the coprimality of `q` and `b=q-1` give a
positive first Pell root, `q^3 | Y` and `b | Bt`. The three remaining
residuals supply exactly the other displayed hypotheses of **Cal**.

Assuming Cal, `X>=q^2`; positivity gives `C>=1` and `F<=q-2`, hence
`Bt-C >= q^2-1-(q-2)*q = 2*q-1 > 0`. The positive coordinate assignment
`r_old=rho+k*(Bt-C)` makes the first roots equal algebraically, and the other
three residuals are independent of `r`. This map is therefore valid under Cal.
The literal-to-Cal orientation, q^4 congruence, common Pell indices and
power-recovery bindings remain open as the author explicitly states; the
closely related compact/source argument is not itself a completed application
to this graph and current tuple.

## Parent-to-candidate map

For a positive parent zero, the first norm and positive first-root coordinate
force `Bt>0`; square divisibility gives `Y=q^3*s`, `Bt=b*t` with positive
s,t. The common main norm rules out `k=2` by the cited consecutive-square gap;
the cited first-Pell descent then yields `k>=8*m+4` and
`tau-ell>k/4>2*s`. Since `Bt>0` and `X+K0*q>0`, also `C>=1`.
Consequently
`rho=(C-1)*k+(tau-ell)-s+t` is positive and direct substitution makes
`Znew=M*tau`. The other three residuals are unchanged. This direction may
switch the first-root sign and does not require the direct inverse coordinate
to remain positive; it has no Cal premise.

These are ordinary-integer arguments with the stated port and source-theorem
assumptions. They are not a new model-theoretic formalization. In particular,
this review does not prove Cal, replay provider ancestry, certify the cited
source theorems in the current environment, identify the printed document in
Lean, or show consistency of ZFC.

Reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/adaptive87-current-cfold88-degree28-independent/check.py | cmp - reviews/adaptive87-current-cfold88-degree28-independent/receipt.json
```

The review executes no Lean or build and does not modify the candidate.
