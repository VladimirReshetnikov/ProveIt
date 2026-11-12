# Independent source review: forced first-root coordinate

The two signed-branch `linear_combination` certificates have the correct signs. From the represented signed root and `P=b*t`, the positive sign yields `k*(P-1)+t+tau=ell`; the negative sign yields `k*(P-1)+t=ell+tau`. Cancellation explicitly requires positive b, and the cast of `P-1` explicitly requires `P>=1`. These branches match the source's natural-coordinate contradiction.

The plus branch contradicts `tau>ell`. In the minus branch the draft uses the corrected bounds `k*(P-1)<ell` and `t<ell`, so their sum is less than `2*ell<ell+tau`; it does not rely on the previously false inequality `k*(P-1)+t<=k*P`. The square norm implies tau>ell by the displayed polynomial comparison. The separate P<m lemma has explicit natural-model assumptions including `K+1<=q²`, `C<q`, `F>0`, the represented P identity, `q>=2`, `X>=1` and `Y>=q³`; its order chain is valid under those assumptions.

This is a fact-level proposal: actual graph extraction, P and K representation, the compact kernel inequality and signed quotient/root witnesses remain separate obligations. The source's ring identities and finite controls were independently checked and the author's receipt reproduces. No Lean elaboration, axiom reports, provider ancestry or iPRA endpoint has been established. The alternative root-switch route is existential and has separate obligations.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-residue89-r-model-independent/check.py | cmp - reviews/ordinary13-residue89-r-model-independent/result.json
python3 -I -S -B research/ordinary13-residue89-r-model-draft/check.py | cmp - research/ordinary13-residue89-r-model-draft/receipt.json
```
