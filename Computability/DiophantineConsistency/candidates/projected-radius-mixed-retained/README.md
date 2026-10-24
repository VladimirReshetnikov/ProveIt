# Retained raw coefficients,107 guards and a literal994 bridge

This new sibling combines the mixed comparison-domain normalization
with the two independently derived A/D signs. It preserves every
original raw row and coefficient; its unprojected height remains427.

| Directory | Integer variables | Quadratic rows | Collected terms | Height |
|---|---:|---:|---:|---:|
|`retained`|1580|1284|5392|427|
|`support2_affine1`|933|637|4236|4750|
|`support2_affine2`|788|492|6000|737653|
|`support4_affine2`|724|428|9350|737653|
|`support8_affine2`|710|414|9314|938261|

Each is a fully materialized degree4 polynomial over unrestricted
integers, with complete collected coefficients and signed integer
restoration certificates. Each improves its frozen159-guard analogue
by156 coordinates,52 rows and780 terms at unchanged height.

The primary proof is explicit:107 guards plus four exact original-row
bounds supply the109 guard values of the already sealed994 equation.
All107 witness transfers and the two fresh A/D triples are bound to
literal slots. The complete592-wire integer raw/667 map is checked.
The994 theorem then supplies signed-index recovery and its positive
comparison normalization. No raw pointwise all-natural claim is used.
See `PROOF.md` and `BRIDGE994.json`.

A fresh976-step sign/private-use ledger supplies additional direct
evidence. It explicitly recovers B from its defining gate before
using bq orientation, so no sign circularity is hidden. Integer
projection inverses restore every parent coordinate and every guard
before the bridge is applied.

Reproduce from the repository root:

```
python3 -B Computability/DiophantineConsistency/candidates/projected-radius-mixed-retained/build.py --check
python3 -B Computability/DiophantineConsistency/candidates/projected-radius-mixed-retained/check.py
```

Both also pass with `-O`. The independent checker imports no optimizer.
All source copies, arithmetic engines and ordinary proof dependencies
are pinned. Frozen159/994/706 parents and canonical pages are unchanged.
No Lean, old H10 emitter or new internal-ZFC endpoint is claimed.
