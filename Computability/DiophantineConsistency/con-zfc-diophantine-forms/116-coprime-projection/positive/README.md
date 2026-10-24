# Coprime Pell fusion: 10 positive variables, 96 operations, degree 266

A structural improvement of the pinned direct positive-variable equation:

| construction | strictly positive variables | live binary operations | exact degree |
|---|---:|---:|---:|
| latest multiplicative-base expanded transport | 10 | 98 | 368 |
| latest direct-base expanded transport | 10 | 103 | 340 |
| new coprime first/strong fusion | 10 | 96 | 266 |

The output is the single polynomial `N=0` in `equation.json`. It has
57 multiplications, 20 additions and 19 subtractions, all counted as
binary operations, including multiplication by fixed integers.
The ten quantified inputs are J,F,alpha,i,T,x,Y,n,eta,zeta, all strictly
positive. The four port payloads are fixed coefficients, not variables.
The unexpanded arithmetic-circuit format avoids printing giant coefficients.

The 96-operation schedule also uses the exact expanded-transport identity
P=q³*q(q-1), W=1+q(q-1)L: move the integral -L*B term beside n+V
and compute the remaining transport with B rather than W*B. This saves
two operations from the original fused98 evaluator without changing its
polynomial. The frozen98 graph and proof remain in source/; check.py
checks the entire row map and universal carrier identity. The comparison
rows use the later upstream expanded-transport results at commit49379c31d.

The new strong radicand is

    Df=1+Delta*Dtau*(i*c²)².

It is coprime to Dtau. Packing their product into one radical forces
both factors to be squares, permitting the actual strong Pell ordinate
sqrt(Dtau)*i*c². This reduces the norm from three radicals to two, hence
from octic to quartic. A polynomial transport majorant absorbs the larger
root product. Completeness uses a recurrence-matrix period modulo
sqrt(Dtau)*c² to construct positive strong witnesses.

The proof is in PROOF.md. The exact leading coefficient is

    [J^126*x^32*i^10*Y^62*eta^32*alpha²*F²] N = 2^14*beta^126 > 0.

The raw, uncancelled syntactic bound288 is NOT the exact degree266.

## Reproduce

Only Python 3's standard library is needed:

    python -B build.py --check
    python -B check.py
    python -B -O build.py --check
    python -B -O check.py

The stored CHECK receipts include full universal norm and centered
cancellation coefficient checks, whole literal circuit auditing, coherent
coefficient payload hashes, 24 exact independent formula controls,
3 actual-payload modular controls, nonzero leading homogeneous witnesses,
6 concrete positive Pell-period/fused-root examples, 64 signed old/new
whole-polynomial controls, and 5 rejected
mutations. These finite controls supplement, not replace, the ordinary
unbounded proof.

## Fixed-source provenance and limitations

The frozen parent is VladimirReshetnikov/ProveIt commit
84e16e43092614bae262ca59651cb9d77e31a255,
Computability/DiophantineConsistency/candidates/ten-positive-direct-zero-offset.
Source: https://github.com/VladimirReshetnikov/ProveIt/tree/84e16e43092614bae262ca59651cb9d77e31a255/Computability/DiophantineConsistency

The copied parent and ordinary proof dependencies are in source/.
The coefficient files retain the original coherent compact44 tuple,
including the already shifted MF. This tuple's K0 is not the repaired
BFS44 K0; the two are never identified or mixed.

Both directions of positive-zero/refutation equivalence are ordinary
mathematical arguments with the inherited source61/native/compiler
calibration explicitly retained. This is no new machine-checked Lean
endpoint or encoded internal-ZFC certificate, no assertion of consistency,
and no claim of global minimality. None of the upstream repository's
files has been modified. The task's ambient natural-language statement
of provability in ZFC inherits precisely that source calibration.
