# Residue-90 f/y model forcing draft

This source-only packet proposes that every zero of the exact 13/90 graph has
`f>0` and `y>0` in an ordered IΣ₁ model. **It has not been elaborated by
Lean.** Its graph identities, model arithmetic tactics and imported provider
closure are unverified proof attempts.

The literal shifts give `q>0`, `Y>0`, `k>0` and `c≥2` without assuming
positive beta, J, X or gamma. With `I=c²*(i+1)` and `Qnat=I²`, the draft
proposes `Qnat≥4`. Graph strong residual 3 is expanded to
`ι Qnat = ι Delta*((ι f)²−1)`; the positive Delta and Qnat then exclude
`f=0` using the earlier generic arithmetic lemma.

Graph auxiliary residual 2 uses the graph's actual **signed** ordinate and
signed rank. The draft obtains a natural magnitude for that ordinate with
`ReducedNormSigned.natural_magnitude_square`, substitutes the strong residual,
and reflects the resulting equation to model naturals. If `y=0`, it gives
`Qnat*z²=1`, contradicting `Qnat≥4`; this uses the previous source-only
arithmetic helper. Natural representation of the four graph ports is explicit;
the local mathematical identities do not require their signs.

The packet's checker pins the source and inherited graph drafts, rechecks
external graph evidence, and controls the strong/auxiliary identities on
finite natural inputs. It does not run Lean, establish a nonstandard-model
proof, authenticate compact ports or providers, or prove an iPRA endpoint.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-residue90-fy-model-draft/check.py | cmp - research/ordinary13-residue90-fy-model-draft/receipt.json
```
