# One loop for unordered affine proof certificates

This component improves the **source** of package 68. It does not claim a new
measured ordinary Diophantine equation.

The source theorem and its proof are in `single_loop.tex`. Compared with the
two-loop source, truth padding makes the proof horizon also bound every
row-label sum. One joint slack replaces the three separate label slacks.
One bounded loop checks both the proof transition and the common-multiple
divisibility condition.

| Measure | Package 68 | This source |
|---|---:|---:|
| Outer natural parameters | 5 | 4 |
| Bounded universal blocks | 2 | 1 |
| Local natural witnesses | 23 | 22 |
| Local polynomial degree | 50 | 50 |
| Final polynomial witnesses/operations | unmeasured | unmeasured |

The finite regression command is:

```
python3 single_loop.py
python3 -O single_loop.py
python3 build_local_adapter.py
python3 -O build_local_adapter.py
```

Both commands use explicit runtime checks; `-O` does not disable validation.
The output `SINGLE_LOOP_CHECKS.json` includes a complete small artificial
certificate. No ZFC refutation is constructed or assumed.

`build_local_adapter.py` generates the literal local source JSON from the
pinned upstream `affine_shared_step.json`. It verifies that file's SHA-256
before importing it. The packaged `upstream/affine_shared_step.json` is a
byte-exact input, so the default command is fully offline and portable. An
explicit checkout root is also accepted as the optional argument. The JSON
contains the old polynomial, its joint label bound and divisor residual, and exact interface
metadata. It remains a local relation, not a completed final equation.

## Provenance

Repository pin: `2605669a532342f153b13eb6b4a0af4b54f5fa37`.

The inherited local rule polynomial and old affine-flow theorem are from:

- [Shared affine source](https://github.com/VladimirReshetnikov/ProveIt/blob/2605669a532342f153b13eb6b4a0af4b54f5fa37/Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/direct/affine_shared_step.json)
- [Affine product theorem](https://github.com/VladimirReshetnikov/ProveIt/blob/2605669a532342f153b13eb6b4a0af4b54f5fa37/Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/direct/AFFINE_PRODUCT_CERTIFICATES.md)
- [Commutative Horn-flow theorem](https://github.com/VladimirReshetnikov/ProveIt/blob/2605669a532342f153b13eb6b4a0af4b54f5fa37/Computability/DiophantineConsistency/con-zfc-diophantine-forms/68-joint-positivity/direct/COMMUTATIVE_CERTIFICATES.md)

The new part is the padded single-horizon construction and its adapter;
this is not a claim of historical priority. The full internal-ZFC transport,
local-calculus calibration, arithmetic closure, and final measured polynomial
remain separate tasks.
