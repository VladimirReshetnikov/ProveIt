# A direct589-variable quartic for Con(ZFC)

The complete ordinary integer polynomial is

    Q589(z_0,...,z_588)=sum(q_j(z)^2, j=1,...,371).

Its full quadratic residuals are in `support8_default/equation.json`.
The independently collected8,157 monomials are in
`support8_default/polynomial.json`. The degree is exactly4 and the largest
absolute coefficient is2,445,790,974,704.

`PROOF.md` proves equivalence to the complete pinned75-predicate source
and explains its inherited ordinary ZFC-consistency calibration. The new
step shares sign orientation across seven pairs whose sums agree with
independently nonnegative anchors. It uses no power interpretation to
recover those signs. Fourteen scalar guards become seven product guards.

The original source equation and its complete domain certificate are
included in `source/`. `SOURCE.json` pins every inherited input to commit
`84e16e43092614bae262ca59651cb9d77e31a255`. The source theorem is inherited
from the reviewed direct C222 branch, which uses neither K215 nor Jones's
universal equation. The present work is an ordinary mathematical proof
with exact algebraic certificates; no new Lean/Rocq endpoint is asserted.

## Reproduce

Only Python3's standard library is required. Run from any directory:

```sh
python3 build_equal_sum.py --check
python3 check_equal_sum.py
python3 -O check_equal_sum.py --output INDEPENDENT_CHECK_OPTIMIZED.json
```

The generator imports the unchanged pinned optimization engine. The
independent checker imports neither generator nor engine. It checks the
complete source/guard boundary, every row identity, every integral inverse
substitution and every expanded coefficient. It rejects three targeted
corruptions. `INDEPENDENT_CHECK.json` and its optimized counterpart retain
the successful results.

## Other complete equations

| Folder | Integer variables | Quadratic residuals | Quartic monomials | Coefficient height |
|---|---:|---:|---:|---:|
| support8_default |589|371|8157|2445790974704|
| support16_affine2 |601|383|7070|964213|
| support8_affine2 |608|390|7061|938261|

The589-variable result improves the pinned604-variable,9676-monomial
direct quartic without increasing coefficient height. It is not a global
minimum claim. The two other rows are explicit coefficient-height
alternatives. All artifacts contain ordinary finite integer coefficients;
there is no hidden proof predicate in the displayed polynomial.
