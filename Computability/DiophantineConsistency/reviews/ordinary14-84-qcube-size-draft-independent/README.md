# Independent source review: q-cubed size

Positive J and beta give a positive product, and the revised source explicitly
uses model discreteness to obtain `J*beta≥1`. Thus `q≥2`; multiplying ordered
nonnegative bounds gives `q²≥4` and `q³≥8`, and positive s gives `s≥1` and
`Y=q³s≥8`. The stated bound is sharp at `beta=J=s=1`. All positivity
hypotheses are needed for this uniform bound: taking any one of those values
to zero gives a counterexample.

The checker pins the final revised source and graph definition, replays the
author receipt, and independently checks a bounded grid and boundaries. This
is source and finite review only: arithmetic tactics and ordered-model
instances have not been elaborated in Lean, and no graph zero, port binding,
provider compatibility or iPRA endpoint is established here.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-84-qcube-size-draft-independent/check.py > /tmp/qcube-size84-independent.json
cmp /tmp/qcube-size84-independent.json reviews/ordinary14-84-qcube-size-draft-independent/result.json
```
