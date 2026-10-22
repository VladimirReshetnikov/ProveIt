# Twelve positive unknowns for ZFC consistency

This package constructs a fixed polynomial **P12 in twelve strictly positive
integer unknowns**, with exact degree **2601** and a **167-operation**
division-free arithmetic circuit. By the ordinary mathematical proof in
`report.pdf`, composed with the identified ProveIt compiler and K215
calibration results,

> ZFC proves: P12 has no positive integer solution if and only if Con(ZFC).

The package also gives a three-equation version, two reductions over
unrestricted integers, and a smaller complete coefficient tuple. It is
prepared for incorporation into ProveIt; it does not change the repository
or claim a new proof-assistant verification.

## Improvements and tradeoffs

| Construction | Domain | Unknowns | Equations | Degree | Binary operations |
|---|---|---:|---:|---:|---:|
| Existing minimum-operation equation | positive integers | 15 | 1 | 155 | 67 |
| Existing weighted amalgamation (09) | positive integers | 13 | 1 | 571 | 84 |
| **New primitive-element system** | positive integers | **12** | 3 | 2592 | 163 |
| **New primitive-element product** | positive integers | **12** | 1 | 2601 | 167 |
| New primitive-element sum of squares | positive integers | 12 | 1 | 5184 | 170 |
| Existing signed product (14) | unrestricted integers | 29 | 1 | 188 | 121 |
| **New even-weight product** | unrestricted integers | **27** | 1 | 1116 | 139 |
| **New signed primitive-element system** | unrestricted integers | **26** | 3 | 5248 | 225 |
| **New signed primitive-element product** | unrestricted integers | **26** | 1 | 5265 | 229 |
| New signed primitive-element sum of squares | unrestricted integers | 26 | 1 | 10496 | 232 |

Operations count binary addition, subtraction and multiplication, including
products by fixed numerals. Reuse and comparisons in systems are free.
System degree means maximum residual degree. These are circuit sizes, not
bit-operation costs or expanded monomial counts.

The variable improvements are within the inspected explicit compiler family.
General nine-natural-variable and eleven-integer-variable representation
results exist; this package makes no global optimality claim. The existing
67-operation equation remains smaller to evaluate, and the existing
low-degree lifts remain preferable if degree is the primary objective.

The new compiler uses **5,252 tiles** instead of 37,075 and
**B = 2^(5^16)** instead of 2^(5^18). The bit length of B-1 decreases
exactly **25-fold**, from 3,814,697,265,625 to 152,587,890,625. The constants
are still enormous. They are specified by exact finite formulas and an
authenticated tile list, not materialized. This whole tuple can also be
used by the included original 67-operation circuit.

## The equation and its idea

The twelve unknowns are

`J, F, alpha, z, h, i, T, s, w, eta, zeta, t > 0`.

The compact equation is

`P12 = N_index * N_transport * (1 + R_norm) - 1 = 0`.

All three factors are specified by the article and the complete JSON
circuits. `R_norm` eliminates four algebraic coordinates: the main-root
quotient gamma and three Pell roots tau, y, f. One retained coordinate t
encodes `gamma + tau + weight_y*y + weight_f*f`. Explicit polynomial
weights separate all sixteen branches. A rational encoded sum therefore
forces every coordinate to be rational. A special Pell integrality lemma,
followed by the integral encoding relation, recovers the exact integer
quotient and all roots. The norm is a square modulo four, making the
product finalizer sound. A plain resultant without these arguments would
not suffice.

For 26 unrestricted integers, seven positive guards use independent
copies of `Pos(x,y,z)=1+x*x+x+y*y+z*z`; the other five coordinates are free.
The changed weights work before excluding w=0 and with signed T and i.
For 27 integers, an even weighted three-root amalgamation keeps gamma
and achieves substantially lower degree.

## Fixed instance and domains

`INSTANCE.json` is the authoritative package binding. The four fixed ports
are `Bm1 = B-1`, `Kconstant = DC+B*DR`, `MC`, and **shifted**
`MF = MF_natural+B-1`. Use all four from the same recipe in
`compiler/PRUNED_T4_CONSTANTS.json`. The port values are fixed integers;
they are not free parameters of the consistency equation.

Do not mix coefficient ports from different layouts. A complete inherited
tuple is available as a conservative alternative; the new proof notes
identify the interface needed for that substitution. Merely satisfying
the elementary mask congruences is not enough to establish compiler
semantics for an arbitrary tuple.

JSON rows are `[name, operator, left_operand, right_operand]` in dependency
order. Integer operands are literal constants; strings refer to supplied
inputs, fixed ports or earlier registers. `output` is the polynomial to
set to zero; `comparisons` gives the exact equations for a system.
Intermediate registers are abbreviations, not extra unknowns.

`compiler/coefficient_residues.py --modulus N` evaluates the four fixed
ports modulo N without expanding them. It is useful for exact modular
evaluation of the delivered circuits.

## Reproduction

Python 3.10 or newer is sufficient; the new Python programs use only the
standard library. A usual LaTeX installation is needed to rebuild the PDF.

```sh
python3 verification/check_package.py
make verify
make degrees
make pdf
```

The first command authenticates the delivered manifest, checks inherited
source pins, checks circuit structure and recomputes the generator outputs
in memory. `make verify` reruns the finite compiler and independent algebra
checks. `make degrees` repeats the slower modular degree corroboration.
`make pdf` compiles the article. Running a regeneration target can update
receipt formatting; `SHA256SUMS` authenticates the original delivered
snapshot rather than future regenerated files.

The compiler checker deliberately refuses `python -O`, because it uses
assertions. The arithmetic checkers use explicit failures and remain active
under `python -O`. Neither the finite checks nor generic-line degree
specializations replace the universal mathematical proofs.

## Contents and review order

1. Read `report.pdf`, especially the proof boundary in Sections 1 and 5.
2. Inspect `proofs/PRIMITIVE12_PROOF.md`, the separate integer proofs, and
   their independent review notes.
3. Inspect `compiler/PRUNED_T4_PROOF.md` and its exact recipe and checker.
4. Trace substantive imported results using `SOURCE_PINS.json` and the
   bundled `inherited/` notes.
5. Inspect the arithmetic JSON and run the reproducible checks.

`machine/KEndpoint215.lean` identifies the imported endpoint; its full
build dependencies stay in ProveIt. The machine table and notices are
included. All source pins refer to
`f0ae4e0991ca44a7bb4e5671d42e33d775e48035` of
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt).

This is AI-assisted ordinary mathematical research, with independently
assigned mathematical reviews and finite algebra checks. It is not a new
Lean/Rocq formalization, a proof of Con(ZFC), or an assertion that a halting
K215 computation has been found. The inherited machine endpoint has its
own formal verification records, distinguished from this new bridge.

## Suggested repository integration

Keep this package together under a new numbered report directory, for
example `16-primitive12/` if that number remains available. Add the new
rows to the comparison README, explicitly retaining the 67-operation,
low-degree, and general universal-representation caveats. The four-port
binding should travel with every copied arithmetic circuit. Preserve
`SOURCE_PINS.json`, the literal table hash, proof dependency notes, and
inherited notices. No existing report needs to be replaced to use these
new alternatives.
