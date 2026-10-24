# Measured intermediate reductions

These are ordinary research probes, not alternate definitions of the
final `affine/` and `retained/` equations. All started from the frozen
fixed-W parent and combined the same beta bound `H=E+F`.

| Probe | Naturals | Quadratic rows | Degree | Terms | Height |
|---|---:|---:|---:|---:|---:|
| `Z=z0+1`, delete a2, affine | 3,383 | 2,778 | 4 | 15,904 | 127,300,337 |
| `Z=z0+1`, delete a2, retained | 5,904 | 5,299 | 4 | 16,835 | 1,827 |
| Unshifted Z, delete a2 only, affine | 3,383 | 2,778 | 4 | 15,454 | 127,299,880 |
| Unshifted Z, delete a2 only, retained | 5,849 | 5,244 | 4 | 16,560 | 1,772 |
| **Unshifted Z, delete both, affine** | **3,328** | **2,723** | **4** | **15,289** | 127,299,660 |
| **Unshifted Z, delete both, retained** | **5,739** | **5,134** | **4** | **16,230** | **1,552** |

The first probe is sound: `Z=z0+1` in the last norm forces `A>W`, and
the canonical completeness quotient Z is positive. Its literal normal
and optimized audits passed. It is superseded because A>=2 already
follows from `T>0` and the T definition; introducing the positive-Z
addition gate is unnecessary. The unshifted a2-only intermediate also
passed its literal normal and optimized audits. The final additional
b2 deletion uses the retained norms, `V>=Y` and `S=X mod U`, as proved
in `PROOF.md`.

All listed coefficients, term counts and full SOS expansions were
materialized. Only the final both-slack candidate is proposed for a
frozen checkpoint. These local savings do not alter the inherited
ordinary C222 calibration or extend the paused Lean development.
