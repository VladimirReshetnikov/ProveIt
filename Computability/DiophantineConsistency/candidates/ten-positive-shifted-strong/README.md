# Ten positive unknowns, 102 operations, degree388

This complete sibling has **10 strictly positive integer unknowns, 102
operations and exact total degree388**. It retains the entire authentic
original compact44 coefficient tuple. The complete polynomial is the
acyclic arithmetic schedule in `equation.json`; all102 gates, ten inputs
and four fixed coefficient ports are live. There are59 multiplications,
25 additions and18 subtractions.

Relative to the frozen free-J103/408 endpoint, the two changes are

    I=(i+q^2)c^2,     L=H*I+b.

The shifted input guarantees I>=mu*c^2 and c^2|I for every positive i,
without assuming mu|I. These are precisely the old soundness premises.
The shorter transport uses a bound proved before q parity and before
rho=e/mu^2 is known integral: |e|<b, hence |rho|<b/2. It excludes a
negative transport coordinate with the smaller L. `PROOF.md` supplies
this unbounded argument and both positive witness constructions, including
a fresh final n coordinate in completeness. It rebuilds the inherited
source61 witnesses rather than dividing the new multiplier by mu.

The exact algebraic comparison with the whole103-operation parent is

    i_child=mu*i_parent-q^2,
    n_child=n_parent-(I_parent+c*T')*Bt.

Under this substitution all core, radicand, carrier and output registers
agree; L_child=L_parent-I-c*T'. The n substitution need not preserve
positivity at arbitrary inputs. The separate canonical completeness
argument constructs positive n and is essential to zero-existence
equivalence. `CUTS.json` accounts for every parent and child row.

The leading part of the complete polynomial is omega0^4, where

    omega0=2^7*q0^56*w^10*Y^19*(eta+zeta)^10
                  *(q0-F-alpha)*(q0-F),   q0=beta*J.

Consequently the selected degree388 coefficient is

    [J^224*w^40*Y^76*eta^40*alpha^4*F^4]P=2^28*beta^224>0.

The independent checker expands all35 terms of the octic norm and its
complete centered expression, verifies every literal cut and operand,
checks this leading coefficient, and checks full degree388 slices with
the actual four coefficient payloads. It also checks120 actual-port
input-map controls,50 exact signed free-port controls and corrupted
input/norm controls. Such controls check transcription; the unbounded
proof and explicit algebraic identities supply the general argument.

Every copied proof, source theorem, source notice, ordinary peer and BFS
transfer file is compared byte for byte with its pinned repository
source. The whole frozen parent manifest is checked. Four compressed
payloads are included with raw and compressed hashes. No coefficient
emitter or Lean process is executed.

The proof also applies to the separately calibrated whole BFS44 page
tuple, with beta>=31 and its full typed-color/native/controller transfer.
That tuple has a different K0. The polynomial here uses the original
whole compact44 tuple and does not assert pointwise equality of the two
K0 coefficients or mix them. A later page may use the BFS tuple through
this uniform arithmetic proof.

The inherited ordinary native/compiler/refutation equivalence is
retained, with a separate focused mathematical peer under
`source/SHIFTED_ORDINARY_PEER.*`. No new Lean or encoded object-ZFC
proof, proof of consistency, or claim of optimality is supplied. The
canonical page and all frozen endpoints remain unchanged.

Run from the repository root:

```sh
python -B Computability/DiophantineConsistency/tools/build_ten_positive_shifted_strong.py --check
python -B -O Computability/DiophantineConsistency/tools/build_ten_positive_shifted_strong.py --check
python -B Computability/DiophantineConsistency/candidates/ten-positive-shifted-strong/check.py
python -B -O Computability/DiophantineConsistency/candidates/ten-positive-shifted-strong/check.py
```
