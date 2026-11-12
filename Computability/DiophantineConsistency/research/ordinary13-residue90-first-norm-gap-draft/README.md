# Residue-90 first-norm C gap: source-only model draft

`Residue90FirstNormGap.lean.src` proposes that a zero of the exact 13/90
residue graph forces `F+alpha<q`, and hence positive signed `C`, when `J>0`
and beta is a positive model natural. **The source has not been elaborated by
Lean**; its ordered-ring tactics, graph norm import and provider ancestry all
need checking.

The theorem takes a natural four-port tuple `p` and forms its signed graph
ports by integer casts. This is an explicit representation of all four ports,
stronger than the local mathematical argument needs: only positive beta and
nonnegative represented K0 are used. The literal shifts make `F`, `alpha`,
`eta`, `zeta` and `r` positive, so `k=eta+zeta≥2`.

The proof assumes the opposite inequality. In the model difference ring,
`C≤0` and natural `X,K0` imply `Bt=C*(X+K0)-F<0`. With
`b=J*beta>0` and `ell=m*k`, the graph's **own** first-root expression then
gives `Z>b*(ell+k)≥0`. At the same time

```
(ell+k)² − (1+m*(m+1)*k²) = ell*k+k²−1 > 0.
```

The two strict square inequalities contradict the graph first norm
`Z²=b²*(1+m*(m+1)*k²)`. No root sign or first-norm quotient is assumed.
The first-norm source itself is the separate unelaborated
[`first_ring_norm` proposal](../ordinary13-residue90-norm-model-draft/Residue90GraphNorms.lean.src).

`compact_gamma_of_JX` proposes feeding the derived gap into the earlier
compact-symbolic gamma client. It **retains `J>0` and `X≥1` as hypotheses**,
uses an arbitrary standard-natural `K`, and inherits all signed-norm,
quotient, rank, compact-port and provider qualifications. No fixed-kernel
byte identity, 90/91 zero map, physical/PDF binding or iPRA endpoint is
established by this packet.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-residue90-first-norm-gap-draft/check.py | cmp - research/ordinary13-residue90-first-norm-gap-draft/receipt.json
```

The checker pins source/graph bytes, reruns the inherited finite source
checks, and controls the displayed strict inequalities on finitely many
ordinary-integer cases. It does not execute Lean, stage artifacts, validate
these proofs in nonstandard models or authenticate providers.
