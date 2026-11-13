# Eta-natural 85 prototype: zeta-zero boundary probe

This packet investigates the *exact structural boundary*, without claiming a
new equation or zero-equivalence. It generates `probe.json` from the pinned
85-row eta-natural prototype by allowing zeta itself to be a nonnegative
input. In the original graph `zeta=n_zeta+1`, `k=eta+zeta`, and
`r0=k−1−R`. The probe removes the `k=eta+n_zeta+1` increment, uses
`k=eta+n_zeta`, and inserts the corresponding subtraction of 1 in `r0`.
Both graphs have 85 arithmetic rows; no operation reduction or iPRA theorem
is asserted. Under `probe.n_zeta=old.n_zeta+1`, all displayed quantities and
the output agree by the exact row substitution. The checker validates
row topology and 160 modular evaluations in that forward direction.

Two **entire-graph zeros** at eta=zeta=0 have been checked by exact integer
evaluation of all 85 probe rows. All 13 witness coordinates are
nonnegative, in the order `n_J,n_F,n_alpha,n_f,n_i,n_T,n_w,n_s,n_r,n_eta,
n_zeta,n_y,n_gamma`. Port order is `(beta,K0,MC,MF)`:

* Witness `(1,0,0,1,0,0,0,0,0,0,0,1,0)`, ports `(-1,0,1,0)`.
  It has q=0, Y=0 and output zero; the old 85 graph at the same tuple has
  output 9. Its negative beta violates the natural/compact first port.
* Witness `(1,0,0,1,0,0,1,0,0,0,0,1,0)`, ports `(0,-2,-1,0)`.
  It has q=1, Y=1 and output zero; the old graph at the same tuple has
  output 97. Its negative K0 and MC violate the natural compact tuple, and
  its beta is not strictly positive.

For both probe evaluations the exact first/main residuals A0=A1=0, the
strong residual is 0 and the auxiliary factor Fa=1, so this is a full output
zero, not just a partial factor assignment or a bounded search hit. These
examples disprove a blanket zeta>0 implication for **arbitrary signed ports**.
They do not show a zero at the authenticated compact ports, refute an
existential zero-map that may change witnesses, or establish anything about
IΣ₁ models with natural represented ports and compact beta. The old graph's
nonzero value is only for the *same* witness and does not prove it has no
other zero.

At compact natural ports the previously proposed J>0 and q≥2 graph arguments
would need to be rebound to this altered literal. The eta-zero parity route
also used zeta>0, so it cannot be imported unchanged for the simultaneous
eta=zeta=0 boundary. For eta>0 and zeta=0, k=eta and c=eta*(1+Y); proving
or disproving the desired same-model forcing or a replacement-witness map
remains open. Any proof must supply graph-unit/port casts, model arithmetic,
provider and endpoint bindings. No Lean execution, PDF binding, compact-port
full-zero claim or reduction has occurred.

The receipt records the complete witnesses, ports and selected exact
intermediate values. Reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-eta85-zeta-zero-boundary-audit/check.py | cmp - research/ordinary13-eta85-zeta-zero-boundary-audit/receipt.json
```
