# Fourteen unrestricted integers,117 operations, degree312

This new sibling replaces the frozen119-operation parent's guard
`Pair(v²G,eta*zeta,t)=Pos(p1,p2,p3)` by `Pair(G,eta*zeta,t)=Pos(...)`.
It removes exactly two live multiplications. The complete new polynomial
in `equation.json` has144 live nodes:66 multiplications,26 additions and
25 subtractions, with all14 unrestricted integer inputs and six fixed
coefficients used.

The full norm/core is unchanged. The two complete outputs are generally
different polynomials; their integer-zero **existence** is equivalent.
The new `PROOF.md` excludes v=0 using its exact first-root value1,
rationalization of the other two roots and a CRT contradiction. Only then
is an old zero restored by regenerating the four private guard witnesses.
The converse regenerates those witnesses for G. No coordinate is deleted
or restricted to positive integers.

The complete highest degree312 homogeneous component is unchanged:
the guard difference has degree at most20, so the output difference has
degree at most304. The identical norm has exact degree256. In particular

```
[j^140 w^48 v^60 h^12 r^16 c^32 z^4] P
  =2^280*3^188*beta^140 >0.
```

The independent checker imports no new builder. It checks every retained
instruction/operand, the explicit guard alias, all144-node coverage,
private-guard independence of the norm, all35 cleared-norm coefficients,
both complete guards and their difference, the strict degree bound,
all six complete coefficient payloads, actual signed controls including
v=0/c=0, exact actual-tuple degree attainment and four bad mutations.
`NODE_REMAP.json` explicitly retires Gv; it never falsely identifies
v²G and G pointwise. `SOURCE_PINS.json` binds the exact frozen119 parent.

From the repository root:

```
python3 -B Computability/DiophantineConsistency/tools/build_constructive_integer14_guard_reduced.py --check
python3 -B -O Computability/DiophantineConsistency/tools/build_constructive_integer14_guard_reduced.py --check
python3 -B Computability/DiophantineConsistency/candidates/constructive-integer14-guard-reduced/check.py
python3 -B -O Computability/DiophantineConsistency/candidates/constructive-integer14-guard-reduced/check.py
```

The two `CHECK*.json` receipts retain the independent normal/-O results;
`VERIFICATION.json` retains all four successful commands. `MANIFEST.json`
seals the complete new packet, including all copied source and coefficient
files. The generator only writes this new sibling and preserves every parent.

The native/compiler/refutation interpretation is inherited from the restored
old integer zero. This is an ordinary arithmetic result, with no new native
calibration, consistency proof, absence-of-zeros assertion, global optimum,
Lean certificate or internal object-ZFC theorem. Lean remains paused; page
files and common documentation remain unchanged.
