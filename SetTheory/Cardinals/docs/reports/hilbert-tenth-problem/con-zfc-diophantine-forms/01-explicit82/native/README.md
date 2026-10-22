# Native Diophantine construction for Con(ZFC)

This directory supplies two fully specified fixed-program constructions:

| Construction | Positive unknowns | Equations | Degree | Arithmetic operations |
|---|---:|---:|---:|---:|
| Main polynomial | 18 | 1 | 187 | 82 = 46 multiplication + 36 addition/subtraction |
| Comparison system | 20 | 9 | At most 42 per equation | 72 = 39 multiplication + 33 addition/subtraction |
| Sum of squares of the comparison residuals | 20 | 1 | 84 | 98 = 48 multiplication + 50 addition/subtraction |

All three use the same six fixed coefficients, defined by the finite recipe in `k215_native_definition.py`. The mathematical construction and proof are in `../report.pdf` and `../report.tex`.

These counts use the repository's shared-expression model: fixed integer coefficients are free inputs, while each binary addition, subtraction, or multiplication is counted. Coefficient bit lengths and coefficient generation are not counted. The constructions are not claimed globally minimal.

## Files

- `k215_native82_source.json`: the complete 82-row polynomial evaluation schedule, its 18 strictly positive witnesses, and its six fixed coefficient ports.
- `k215_native72_system.json`: the complete 72-row schedule and nine comparison pairs, plus the complete 98-row sum-of-squares schedule.
- `k215_native_definition.py`: the concrete normalized K215 machine, tile alphabet, local window predicate, finite window ordering, native compiler, and exact coefficient definitions.
- `k215.tm`: the pinned literal 215-state binary machine, with SHA-256 `fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.
- `audit_native_specialization.py`: independently written checks of the new finite recipe and fixed-input specializations.
- `native_specialization_audit.json`: the deterministic audit output.
- `complete84_scaled_strong_output.json`, `complete74_factored_first_norm.json`, and `complete75_half_binomial_compiler.json`: pinned predecessor receipts, read only as JSON data by the audit. No predecessor Python program is executed.
- `nine_equation_system.txt`: the nine-equation alternative in ordinary mathematical notation.

## Running the bounded checks

Python 3 and its standard library suffice. From the archive root:

```sh
python3 native/k215_native_definition.py
python3 native/audit_native_specialization.py
python3 -O native/audit_native_specialization.py
```

The commands work independently of the current working directory. They do not modify the source files, contact the network, enumerate the full K215 window alphabet, or compute the enormous six coefficients.

The audit checks:

- All 3,496 transitions of the concrete 437-state, eight-symbol normalized machine are defined.
- The 3,510-tile alphabet is distinct, and both marked windows satisfy the local predicate.
- Unary preparation on inputs 1–12 has the intended parity behavior.
- 12,000 K215 steps agree with the folded one-sided simulation.
- Four small compiler layouts match fields in the pinned compiler receipt, including both high-monomial correction branches and a clause-padding case.
- The 82-, 72-, and 98-operation schedules are the exact fixed-input constant folds of their respective predecessor schedules.
- All schedule gates and fixed/witness ports are live; the arithmetic counts are exact.
- 256 complete signed polynomial evaluations agree across the constant folds.

These numerical evaluations are algebra diagnostics. Their arbitrary coefficient assignments are not claimed to encode valid K215 programs, and they are not accepting computation or Pell witnesses. The general equivalence relies on the mathematical invariants and pinned universality theorems described in the report.

## What the coefficient recipe specifies

`k215_coefficients(path_to_k215_tm)` uniquely specifies these six integers:

| JSON port | Mathematical value |
|---|---|
| `Bm1` | B − 1 |
| `Kconstant` | D_C + B D_R |
| `fixed_2d` | 2d |
| `fixed_2d_plus_b` | 2d + b |
| `MC` | The modified native low mask |
| `MF` | The modified native high mask + B − 1 |

The high-mask shift by B − 1 is essential. The bound “native high mask < B − 1” does not apply to the final `MF` port.

The function is an exact finite mathematical recipe, not a practical promise that CPython can finish its enormous enumeration and integer allocation. **The full K215 window alphabet and coefficients have not been materialized.** There is no unspecified choice or existential program index in their definition. The default command intentionally runs only the bounded checks.

The final ordinary input is fixed to x = 1. The native compiler doubles it, so the normalized machine receives raw distance y = 2 and starts with four ones. Start is selector 0 and End is selector 1.

## Domain and proof status

Every supplied witness in both native constructions is a **strictly positive integer**. Some computed intermediates can be signed away from a zero; they are not additional witnesses. Do not simply admit arbitrary signed inputs: that changes the zero set.

For nonnegative unknowns, replace each positive witness v by n + 1. For unrestricted integer unknowns, replace it by 1 + a² + b² + c² + d². These conversions preserve solvability but must be charged separately if operation counts are reported.

The intended equivalence, provable by the mathematical reductions in ZFC, is:

> A positive solution exists if and only if a finite ZFC refutation exists.

Equivalently, lack of a positive solution is equivalent to Con(ZFC). This does not assert or prove ZFC's consistency. The native optimized universality chain and the new composite endpoint have not been kernel-checked here; finite regression tests are not presented as a substitute for that work.

## Provenance

The predecessor constructions and K215 data come from VladimirReshetnikov/ProveIt at commit `cdd582bec13f908df3711fa9e05d1ddac368a5db`. The complete paths and additional proof references appear in the report and archive provenance information. The new contribution here is the concrete coefficient recipe, fixed-input specialization, explicit adapters, and independent checks, not a new universal-polynomial theorem.
