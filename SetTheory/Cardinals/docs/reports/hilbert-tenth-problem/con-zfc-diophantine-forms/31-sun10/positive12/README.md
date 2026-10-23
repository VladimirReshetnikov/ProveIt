# Twelve positive variables: 108 operations, or a 102-operation system

All supplied variables are strictly positive integers. The product has exact
degree 1081. Both systems have exact residual degrees 7, 2, and 1072.

| File | Operations | Interpretation |
|---|---:|---|
| `generated/product108.json` | 108 | Single equation, unshifted transport coordinate |
| `generated/system103.json` | 103 | Three comparisons, unshifted transport coordinate |
| `generated/shifted_system102.json` | 102 | Three comparisons, z_old=z+1 |

`REFACTORED12_PROOF.md` gives the equations and proof. The circuit identities
are exact with the four ports symbolic. The active fixed specialization uses
the complete **wang943-mixed-121x8801** tuple, whose canonical binding and
payloads are in the adjacent `../coefficients` directory. The local binding
maps beta,K0,MC,MF to beta,K,MC,MF_source. The final mask is already shifted.
Historical coefficient tuples inside `upstream/` are source evidence only.

From this directory run:

```sh
python3 build_refactored12.py
python3 check_refactored12.py
python3 audit_coefficients_independent.py
```

The standard library suffices. These commands regenerate the three circuits,
the active binding, and the arithmetic and independent coefficient receipts.
All local paths resolve relative to the scripts, so the same commands also
work with absolute script paths from another working directory.

`SOURCE_PINS.json` authenticates every bundled historical source against its
immutable Git blob and SHA-256 hash. The finite checks establish the displayed
local algebra and literal data. The new proofs compose with the inherited
unbounded compiler and K215 calibration; they do not decide consistency or
constitute a new end-to-end Lean/Rocq verification.
