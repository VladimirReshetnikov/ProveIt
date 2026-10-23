# Ten unrestricted integers: degree 7,428,120 and 525 operations

This optional component applies the new shared-kernel-tap source encoding
to the unchanged package59 Sun finalizer. The resulting fixed polynomial
has no integer zero exactly when ZFC is consistent, by the ordinary
mathematical proof and inherited dependencies stated in [PROOF.md](PROOF.md).

| Quantity | Package59 Sun | This component |
|---|---:|---:|
| Domain | ten unrestricted integers | ten unrestricted integers |
| Exact total degree | 8,469,528 | **7,428,120** |
| Binary arithmetic gates | 533 | **525** |
| Unique kernel taps | 89 | **84** |
| Convolution height | 2161 | **1873** |

The comparison is pinned to ProveIt commit
`beb0192cb8dc36f78c369c080f2adfbc1887a486`. The improvement is in source
coding, with 12.2959% lower degree and eight fewer gates. It does not
establish a new minimum number of integer unknowns or global optimality.

## Reproduce

```sh
python build.py
python verify.py
python -O verify.py
```

Only Python's standard library is required. `generated/sun10.json` is the
literal division-free circuit; `generated/VERIFICATION.json` contains the
checks and exact leading-coefficient certificates. `fixed.py` authenticates
and evaluates the complete old31 coefficient binding. The large fixed
integers are supplied as compressed binary payloads, avoiding decimal
expansion.

Every variable in the circuit is quantified over **all integers**. Named
registers are abbreviations, not extra variables. The sign bootstrap in
PROOF.md explains why the revised source remains valid with that domain.

The `inherited/` files retain their historical claims and numeric parameters
for provenance. The active circuit, layout, source bounds and theorem are
the ones specified by this README, PROOF.md and generated/sun10.json.
