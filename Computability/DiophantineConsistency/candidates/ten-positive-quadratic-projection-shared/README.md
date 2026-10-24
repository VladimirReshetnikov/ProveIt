# Ten positive unknowns, degree408,105 operations

This is an exact **105-operation evaluator** of the frozen
`ten-positive-quadratic-projection` polynomial:61 multiplications,26
additions and18 subtractions. It keeps the same ten positive unknowns,
exact degree408, and all four complete original compact44 coefficient
payloads. Every gate, unknown and port is live. The complete literal
equation is the final `N=0` in `equation.json`.

The first92 gates are unchanged, including the quadratic projection and
transport numerator. The final14-gate octic norm becomes this13-gate
symmetric evaluator:

```
U=fs+fc;        ab=fa+fb;      Po=U-ab;
sc=fs*fc;      aXb=fa*fb;     scab=sc+aXb;
4scab=4*scab;  Po2=Po*Po;     Pe=Po2-4scab;
Pe2=Pe*Pe;     scaXb=sc*aXb;  64scaXb=64*scaXb;
N=Pe2-64scaXb.
```

For arbitrary elements s,a,b,c of any commutative ring,

\[
(s-a-b-c)^2-4\{ab+(a+b)c\}
 =(s+c-a-b)^2-4(sc+ab).
\]

Also `abc*s=(sc)(ab)`. Therefore the old and new inner Pe and final N
are equal polynomials. The prefix is identical, so induction along its
registers proves equality of the **entire endpoint polynomial** for every
input and every port value. This step has no positivity, Pell, divisibility
or calibration premise. It saves one multiplication; no new witness map
is required.

The substantive ordinary result is retained as
`source/ordinary-proof.md`, SHA256
`875c8ad93cf0b8d470f149376f4968aba46206d064b1029c367577a172b9b5e9`.
It recovers the omitted main Pell root by psi folding, resolves the
quadratic projection by a whole-product height bound, and constructs
positive witnesses in both directions. Its independent peer and
normal/-O receipts are copied under `source/`. Thus this packet has the
same ordinary positive-zero-existence equivalence with the older
degree816 endpoint and its native/compiler boundary.

The checker independently expands both complete literal tails and the
product of all eight conjugates, verifies the free inner identity, and
checks the27-term centered expansion's unique weight408 term omega^4.
The106-parent's unbounded leading-form argument transfers through the
exact identity; two actual-tuple degree408 lines are supplemental controls.
The uncentered syntactic bound is464. Complete remaps cover all92 prefix
gates and every old/new tail gate. The checker also verifies all actual
coefficient bytes,100 actual-port whole-circuit controls,50 signed
free-port controls, and two corrupted-tail negative controls. It imports
only the independent sparse-ring helper, not a candidate builder or
author verifier.

`DISPLAY_BINDING.json` contains every105 literal gate for the pending
page renderer. Its inherited binding distinguishes the proof's Pell
parameter from the older page alias A=Am1, and records
`bJ=beta*J=q-1`. No PDF or TeX is certified by this snapshot alone.

The original compact44 K in this packet differs from the separately
calibrated BFS44 page K. This universal evaluator identity applies at
either choice of ports, and the parent's ordinary port-box theorem
applies to both coherent tuples. No equality of their two numerical
specializations is asserted. All frozen parents and page files remain
untouched.

From the repository root:

```sh
python -B Computability/DiophantineConsistency/tools/build_ten_positive_quadratic_shared.py --check
python -B Computability/DiophantineConsistency/candidates/ten-positive-quadratic-projection-shared/check.py
python -B -O Computability/DiophantineConsistency/tools/build_ten_positive_quadratic_shared.py --check
python -B -O Computability/DiophantineConsistency/candidates/ten-positive-quadratic-projection-shared/check.py
```

All pass; `VERIFICATION.json` retains the command receipts and
`MANIFEST.json` seals the packet. No operation minimum is claimed.
Lean remains paused, and the ordinary proof and finite certificates
leave the outstanding internal-ZFC formalization obligation open.
