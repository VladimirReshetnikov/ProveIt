# Nine positive unknowns,723 operations,degree1,158,228

This is an exact three-gate reduction of the726-operation radical equation
arriving in `con_zfc_pell_congruences_2026-10-23.zip`, commit `eae4f1952b`.
The archive SHA256 is
`7c21ff5d05ef52c754399a6e62f37ac7622baa6e82a702d855bfb68d82fc1a4a`.
The pinned parent, its ordinary proof and its license/notice are retained
under `source/`. The parent JSON SHA256 is
`56e8629e1590157e608d5ffafcf3943b925562578fba4854c81d443ed2e54f93`.

The incoming construction expresses the scaled full-radical majorant in a
110-term basis using its existing J and D registers. Its majorant is four
times the one in the earlier1,065-operation candidate, and its final scale
changes accordingly. Thus these two candidates have the same inherited
source interpretation and degree, but different polynomials. Here the
723-operation polynomial is **identical** to its726-operation parent.

The three savings share M*U between P,A, share C*D between E,Lambda, and
reuse the existing R+1 in the index expression. Exact sparse integer-ring
identities and a complete structural remap verify every changed gate and
the final output. All nodes are live. The whole original31 native tuple
and every derived fixed coefficient are retained; compact54 ports are not
substituted. Actual fixed values are reconstructed from the authenticated
binding, and60 signed modular assignments compare all named values as a
transcription diagnostic. A deliberately corrupted rewrite is rejected.

Both commands reproduce the frozen artifacts and pass:

```sh
python3 Computability/DiophantineConsistency/tools/build_radical_jd_shared.py --check
python3 -O Computability/DiophantineConsistency/tools/build_radical_jd_shared.py --check
```

The arriving full release also passed all component stages normally and
with optimized Python. The unbounded radical-cone argument, positivity
before integrality recovery, and subsequent ordinary source interpretation
are inherited from `source/PARENT_PROOF.md`. The algebraic gate saving does
not prove the native/compiler/refutation calibration from scratch or supply
an internal-ZFC derivation. Lean formalization remains paused.
