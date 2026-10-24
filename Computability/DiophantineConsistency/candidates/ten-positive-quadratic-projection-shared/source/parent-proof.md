# Ten positive unknowns, degree408,106 operations

This separate endpoint keeps the ten strictly positive unknowns of the
degree816/122-operation parent, halves the exact degree to **408**, and
uses **106 live operations**:62 multiplications,26 additions and18
subtractions. The original complete compact44 fixed tuple is unchanged.
The literal equation is the final `N=0` of `equation.json`.

The new ordinary proof is [PROOF.md](PROOF.md), independently reviewed
in `source/proof-peer.md` with normal/-O receipts. It proves equivalence
of **existence of positive zeros** with the parent. The two polynomials
are not pointwise equal, and the maps do not assert a zero-set bijection.
No new native calibration or internal-ZFC proof is claimed.

The saving has two mathematical steps. First, the strong and auxiliary
Pell equations already recover `c=psi_A(p)`: classify the odd auxiliary
index, reduce its psi value modulo the strong root f, and fold that index
to `[0,m]`. The bounds `c<=I` and `I+c<f` force equality with a genuine
Pell value. Thus the main-Pell radical can be removed.

Second, replace its projection term by

```
Kquad=X*(X+2*(A-2)*c)-1,
Z/M=n+V+Kquad/H+Y/q^3-W*Bt/(q-1)-e/mu^2.
```

Here A is the proof's scaled Pell parameter, H=4A-5, and Kquad differs
from the fixed native coefficient K0. Once `c=psi_A(R)`, the squared
projection gives

```
H | q^3*(q-1)*(X-2^R)*(2^R*X+1).
```

The ratio bound implies that the absolute value of this **whole product**
is less than H. Therefore X=2^R, without choosing square roots prime by
prime. The strict bound uses q>=32 and r>=30; the actual endpoint gives
r>=48. Explicit constructions of positive n in both directions close
the zero-existence equivalence. All bootstrap and witness-order details
are in the proof, including both signs of the auxiliary coordinate V.

The final octic norm needs only three radicands:

```
N=((fs-fa-fb-fc)^2-4*(fa*fb+(fa+fb)*fc))^2
    -64*fa*fb*fc*fs.
```

Its complete14-gate evaluator is in the JSON. The centered expansion
has27 terms and unique weight408 term omega^4. The nonzero leading form
is inherited from the unchanged degree27 leading part of `Z-M*V`, so the
exact degree is408; the uncentered syntactic bound is464.

`check.py` independently verifies the35-term norm against all eight
conjugates, the755-term exact F16 shift factorization used by the witness
map, and both projection identities. It checks all prefix/tail remaps,
topology and liveness, every coefficient byte,100 complete formula
controls, and four actual-tuple degree408 lines with leading coefficient
omega0^4. Additional finite controls exercise negative-index folding,
main classification and the strict height thresholds. Those controls
supplement the unbounded proof; they do not replace it. The checker
imports no author builder or verifier.

`DISPLAY_BINDING.json` supplies the complete106-gate formula snapshot
for a future renderer. In the older page convention, printed A is
literal `Am1`, one less than this proof's Pell parameter; then
`apc=(A-1)*c`. The inherited122-parent reuse must also be respected:
`bJ=beta*J=q-1` by exact cancellation. Four literal uses already use bJ.
The display snapshot does not certify a PDF that has not been rendered.

The generic proof uses only the stated fixed-port box and the arithmetic
parent theorem, so it also applies to the separately calibrated BFS44
page tuple. Its K and this packet's original K are different numbers;
no equality of those two numerical specializations is asserted. All
frozen parents, PDF/TeX and common documents remain untouched.

From the repository root:

```sh
python -B Computability/DiophantineConsistency/tools/build_ten_positive_quadratic_projection.py --check
python -B Computability/DiophantineConsistency/candidates/ten-positive-quadratic-projection/check.py
python -B -O Computability/DiophantineConsistency/tools/build_ten_positive_quadratic_projection.py --check
python -B -O Computability/DiophantineConsistency/candidates/ten-positive-quadratic-projection/check.py
```

All pass. `VERIFICATION.json` records the commands; `MANIFEST.json`
seals every packet file. Lean remains paused. The ordinary arithmetic
equivalence and finite certificates leave the outstanding internal-ZFC
formalization obligation open. No global minimum is claimed.
