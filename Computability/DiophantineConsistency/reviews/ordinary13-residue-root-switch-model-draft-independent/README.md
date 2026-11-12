# Independent source review: root-switch model arithmetic

The draft's two `linear_combination` signs are correct. At r=0, the assumed positive root would yield `ell=k*(P-1)+t+tau`, impossible for positive represented P and `tau>ell`. The only remaining assumed root sign is negative. Choosing a new `r'=2*tau>0` then changes the actual signed root to its negative and preserves its square. This constructs a new witness; it does not prove the original r positive.

The declarations explicitly assume natural b, P, t, ell, k and tau, b>0, P>0, `P=b*t`, `tau>ell`, the signed root equation and the two possible signs. They do not take an upper bound on K0. The actual graph norm, natural quotient and sign witnesses, unaffected residuals and other forced inputs, and valuation transport are still separate client obligations. The independent graph audit pins those dependencies but does not elaborate them.

Free-ring source certificates were independently verified and the author's receipt reproduces. This does not check Lean elaboration, source/provider ancestry or the internal iPRA endpoint.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-residue-root-switch-model-draft-independent/check.py | cmp - reviews/ordinary13-residue-root-switch-model-draft-independent/result.json
python3 -I -S -B research/ordinary13-residue-root-switch-model-draft/check.py | cmp - research/ordinary13-residue-root-switch-model-draft/receipt.json
```
