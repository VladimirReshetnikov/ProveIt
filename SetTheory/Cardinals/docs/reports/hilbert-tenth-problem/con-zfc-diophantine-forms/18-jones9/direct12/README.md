# Direct twelve-variable Diophantine construction

This directory contains an explicit ordinary polynomial in **twelve strictly
positive integer unknowns** whose nonsolvability is equivalent to Con(ZFC),
provably by the mathematical argument internalizable in ZFC described in the
main article. It combines the native K215 compiler with a new four-root
elimination. It improves the direct thirteen-variable family in unknown
count, at the cost of evaluator size and degree. It is not a global minimum
claim and does not replace the separate nine-variable construction.

| Form | Positive unknowns | Equations | Exact degree | Operations |
|---|---:|---:|---:|---:|
| Polynomial `P12` | 12 | 1 | 1609 | 151 |
| System `Nk=1, Nt=1, R12=0` | 12 | 3 | 1600 maximum | 147 |

The 151 operations consist of 97 multiplications and 54 additions or
subtractions. Every binary operation, including multiplication by a fixed
numeral, is charged. Register reuse, fixed coefficient ports, and final
comparisons are free. The JSON contains a literal division-free circuit;
all auxiliary names in the proof are substituted polynomials, not extra
unknowns.

## Reproduce

Python 3 and its standard library suffice. From the unpacked package root:

```sh
python3 direct12/algebra12_build.py
python3 direct12/algebra12_verify.py
```

Both scripts also work when invoked by absolute path from any other working
directory. Output paths are determined from the scripts' own directory.
The generator writes `radical12_product.json` and
`radical12_system147.json`; the verifier writes `radical12_checks.json`,
all here. Neither requires a network
connection, symbolic-mathematics package, or expanded giant coefficients.

The verifier audits gate operands, checks that all 147 system gates are
live, verifies its three outputs against the product circuit, and compares
the norm circuit with an
independent eight-dimensional radical-algebra computation on 48 signed
assignments. Two modular line restrictions confirm degrees 1600 and 1609.
These finite checks supplement the uniform degree and correctness proofs;
they do not decide whether the final equation has a solution.

## Exact instance and coefficient binding

The authoritative whole coefficient recipe is
[`../coefficients/T4_CONSTANTS.upstream.json`](../coefficients/T4_CONSTANTS.upstream.json),
with the accompanying T4 window list and package-wide coefficient evaluator.
The circuit-to-evaluator port map is:

| Circuit port | Package-wide coefficient port |
|---|---|
| `beta` | `beta = B-1` |
| `Kconstant` | `K0` |
| `MC` | `MC` |
| `MF` | shifted `MF` |

Use all four ports from this one recipe. In particular, the high mask is
the shifted coefficient; the unshifted native high mask is not an
interchangeable input. The astronomical coefficients are exactly specified
finite integers and are not materialized in these files. The diagnostic
tests use small integer ports to check a universal polynomial identity;
those test values are not the Con(ZFC) instance.

## Proof and status

`PROOF.md` gives the complete new reduction. `section.tex` is the matching
article section, intended for inclusion in the package's main LaTeX report.
The proof restricts the old normalized strong multiplier to `H*i`,
separates the algebraic conjugate branches, and recovers integrality using
`gcd(H,Q-1)=gcd(H,ell)=1`. Completeness of the restriction follows from
finite Pell-matrix periodicity modulo `H*c^2`.

The construction depends on the established native-compiler interface and
K215/refutation calibration, plus the source packages' weighted-root
bootstrap and signed-core soundness arguments. In the latter, multiplier
nonzeroness and positivity of `w` suffice here; odd-multiplier and
square-scale parameterizations are not additional restrictions on this
positive-domain equation. The mathematical proof is formalizable in ZFC;
this new Diophantine reduction is **not currently Lean- or Rocq-formalized**.
The formal status of the machine endpoint does not automatically extend to
this reduction. The result is an equivalence, not a proof of Con(ZFC).

## Files

- `algebra12_build.py`: literal circuit generator and integer evaluator.
- `algebra12_verify.py`: independent finite arithmetic audits.
- `radical12_product.json`: generated polynomial circuit and system outputs.
- `radical12_system147.json`: separate three-equation circuit, with all
  product-only finalizer gates removed; each `outputs[j]` equals `targets[j]`.
- `radical12_checks.json`: generated verification receipt.
- `PROOF.md`: complete mathematical derivation and exact degree certificate.
- `section.tex`: LaTeX section for the main article.

Source comparison snapshot:
`f0ae4e0991ca44a7bb4e5671d42e33d775e48035` of
`VladimirReshetnikov/ProveIt`. Package-level provenance supplies the inherited
source files and coefficient-recipe history.
