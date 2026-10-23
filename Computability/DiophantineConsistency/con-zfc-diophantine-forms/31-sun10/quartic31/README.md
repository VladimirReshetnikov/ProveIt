# Thirty-one positive variables: 60-operation system and 125-operation quartic

`QUARTIC60_PROOF.md` gives 22 quadratic equations and their proof. Their
comparison circuit uses 60 operations. The sum of their squared residuals
is a single quartic evaluated in 125 operations. The domain is strictly
positive integers, and the transport coordinate satisfies z_old=z+1.

The active instance is **wang943-mixed-121x8801**. `INSTANCE.json` binds all
four ports to the adjacent `../coefficients/payloads` directory and the full
adapter proof. The aliases are beta,K0,MC,MF = beta,K,MC,MF_source. Historical
bindings in `upstream/` remain evidence only.

Run with Python 3.10 or later:

```sh
python3 build_quartic60.py
python3 audit_signed16_independent.py --signed-dir ../signed16
```

The first command regenerates `quartic31_system60.json`, `quartic31_sos125.json`,
`quartic31_sparse.json`, `INSTANCE.json`, and `QUARTIC60_CHECKS.json`. It proves
all 22 residual identities with exact sparse arithmetic and checks the quartic
degree using its coefficient 1 at tau^4. The second command is a separate
independent formula audit of the adjacent sixteen-integer construction.

`SOURCE_PINS.json` authenticates the preserved source bytes at the stated
repository commit. All code uses the Python standard library. Finite checks
supplement the ordinary mathematical proofs and do not re-formalize the
inherited compiler or K215 endpoint.
