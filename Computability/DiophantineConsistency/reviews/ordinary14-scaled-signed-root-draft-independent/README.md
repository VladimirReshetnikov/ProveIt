# Independent source review: signed scaled root

The proposed theorem preserves both branches of `nonneg_or_nonpos`. In each
branch, the square identity and embedding injectivity yield the natural
scaled square; `scaled_quotient` requires the stated positive scale and
returns `z=U*d` and `d²=n`. Substituting that equality retains the original
branch's sign, including the zero case. No sign orientation is selected.

The checker pins the source and both interface sources, replays the author
receipt, and checks bounded signed squares including zero scale as a boundary.
This is source and finite review only: no Lean elaboration, provider replay,
graph instantiation, physical-file binding or iPRA endpoint is established.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-scaled-signed-root-draft-independent/check.py > /tmp/signed-scaled-root-independent.json
cmp /tmp/signed-scaled-root-independent.json reviews/ordinary14-scaled-signed-root-draft-independent/result.json
```
