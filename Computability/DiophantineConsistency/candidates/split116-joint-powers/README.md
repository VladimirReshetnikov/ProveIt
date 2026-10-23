# The same split116 polynomial with 17 fewer operations

These circuits use exactly the compact54-sharp integer polynomial and
coefficient tuple. A global shared addition chain replaces 107 base-power
multiplications by 90. All other arithmetic gates are retained with their
references remapped.

| Domain | Operations | Add / subtract / multiply | Degree |
|---|---:|---:|---:|
| Nine positive integers | 456 | 162 / 22 / 272 | 1,910,404 |
| Nine natural numbers | 463 | 170 / 21 / 272 | 1,910,404 |

The 86 externally used exponents need only five extra powers:

```
114=57+57, 256=220+36, 565=522+43,
1044=522+522, 1078=1044+34.
```

The four large exceptional targets are then

```
522=266+256, 636=522+114, 1201=636+565, 2279=1201+1078.
```

Every other required exponent is the sum of two smaller required exponents.
The generated receipt lists every exponent identity and every retained gate
remap. The checker independently rederives both circuits' power labels,
checks complete new-node coverage and the output correspondence, audits
topology/liveness/counts, and compares 36 modular assignments per domain.
The exponent and structural certificate describes an equality over every
commutative ring; the modular comparisons are only diagnostics. A Lean
proof of this particular rewrite is being developed separately.

Fixed leaves are bound by the unchanged
[compact54-sharp binding](../split116-compact/compact54-sharp/fixed/BINDING.json).
The generator authenticates both parent DAG SHA256 values and every signed
fixed integer. Their native and derived payload byte counts are unchanged.
The degree follows from equality with the parent polynomial and its exact
degree certificate; this is not a new naive degree walk.

From the repository root:

```sh
python3 -B Computability/DiophantineConsistency/tools/build_joint_power_candidate.py --check
```

The six generated files are sealed in `MANIFEST.json`. The parent artifacts
remain byte identical. This is a local improvement of the formalized split116
recipe; newly arrived wave-nine proposals have additional tradeoffs,
including fewer operations. No catalogue or global minimum is asserted.
Native calibration and the internal ZFC equivalence remain open.
