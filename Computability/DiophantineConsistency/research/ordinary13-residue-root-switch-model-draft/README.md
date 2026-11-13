# Existential residue root switch: model arithmetic draft

This source-only draft gives a second route to a positive first-root input:
**change the witness**, instead of proving the original `r` positive. It
therefore does not assume the compact upper bound on K0. No Lean theorem,
tactic or imported provider has been elaborated for this packet.

At an original `r=0`, the draft assumes model-natural `b,P,t,ell,k,tau`
with `b>0`, `P>0`, `P=b*t`, `tau>ell`, and an actual signed root `z` with

```
z = b*(ell+k-k*P)-P,      z = ± b*tau.
```

The plus sign is impossible: its signed equation forces
`ell = k*(P-1)+t+tau ≥ tau`, contradicting `tau>ell`. For the minus sign,
the draft proposes the explicit positive replacement `r'=2*tau`; its
first root is `-z`, so its first squared residual is unchanged. This is not
a proof that the original `r` was positive.

Graph-level clients still have to extract a natural P and quotient t, the
signed magnitude and `±` representation, and `tau>ell` from the actual
first norm; show the other three residuals and all other forced-coordinate
facts survive changing r; construct the mixed predecessor map; and connect
the parent endpoint. Beta/port representations, gamma/rank hypotheses and
provider ancestry remain inherited. In particular, this fact-level argument
uses no K0 upper bound, but it does **not** remove port assumptions from those
other clients. The separate [root-switch graph audit](../ordinary13-residue-root-switch-model-audit/)
checks the relevant graph dependencies for both parent families and folds.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-residue-root-switch-model-draft/check.py | cmp - research/ordinary13-residue-root-switch-model-draft/receipt.json
```

The read-only checker pins source and graph-audit bytes, checks the displayed
free-ring manipulations on finite signed controls, and reruns the audit. It
does not execute Lean, stage artifacts or authenticate providers.
