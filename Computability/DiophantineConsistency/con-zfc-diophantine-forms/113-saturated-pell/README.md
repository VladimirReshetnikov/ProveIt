# Saturated Pell consistency equations

Research contribution for ProveIt, 24 October 2026.

**Start with `report.pdf`.** Its complete editable source is `report.tex`
and `report_parts/`. All arithmetic programs use only the Python standard
library. The archive contains the fixed coefficients themselves and finite
recipes that reconstruct them; no network or external mathematical package
is needed to check the polynomial specifications.

## Main positive-integer results

| Literal evaluator | Domain | Binary operations | Exact total degree |
|---|---|---:|---:|
| `equations/saturated_upper.json` | 10 strictly positive integers | 92 | 283 |
| `equations/saturated_sharp.json` | 10 strictly positive integers | 93 | 278 |
| `equations/direct_saturated_upper.json` | 10 strictly positive integers | 98 | 258 |
| `equations/direct_saturated_sharp.json` | 10 strictly positive integers | 99 | 254 |

These improve the pinned ten-positive zero-offset parent (99 operations,
degree 368) and its direct-coordinate sibling (105 operations, degree 340).
The 92-operation equation is the recommended first candidate when circuit
size is the main objective. The 99-operation direct sharp equation gives
the lowest degree among the four new positive-domain candidates.

Each row defines a **fixed integer polynomial**. The four coefficient ports
are bound to the entire coherent compact44 BFS tuple. They are not parameters
to be chosen after the unknowns. A gate is one binary addition, subtraction,
or multiplication; multiplication by a constant and squaring both count.
Shared registers are counted once. Coefficient bits are reported separately.

### Mathematical mechanism

Set `E = 1 + V0(V0+1)k^2`, `U = i c^2`, and
`Df = 1 + Delta U^2 E`. Then `gcd(E,Df)=1`. Requiring `E Df` to be a
square recovers both square conditions, with the proof-only old Pell
ordinate `I = U sqrt(E)`. The final two-root norm has four signed factors.
Its exceptional zero-sum cancellation is impossible because it would imply
`E | 1`. A finite Pell-matrix period supplies the additional divisibility
needed for the converse witness construction.

The paper proves soundness, positive completeness, exact global degrees,
and explicit nonzero highest homogeneous forms. It also treats the delayed
divisibility step in the direct coordinate chart.

## Main unrestricted-integer result

**`integer12_saturated/rational.json` has 12 unrestricted integer variables,
123 binary operations, and exact total degree 1084.** It improves both the
pinned rational parent (145/1200) and integral parent (141/1456). This is
the recommended equation when all unknowns must range over `Z`.

The same coprime product reduces its four-root norm to a three-root norm.
The auxiliary term is `4 U E T`; the proof-only substitutions
`I=U tau` and `T_old=tau T` restore the signed source kernel exactly.
Completeness uses full-residue interpolation with modulus parameter
`s tau`, followed by the requested old residue `tau a (mod I)`.
The proof covers every signed input and the exceptional zero cases.

The name `rational.json` describes the norm used during its derivation.
The exported equation is an ordinary integer polynomial with no division
or radicals. `integer12_saturated/integral.json` is a dominated control
with the same 123 operations and degree 1280.

## Unrestricted integer coordinate-shear controls

The `integer12/` packet contains two independent polynomial coordinate
changes of the current scalar-carrier equations:

| Evaluator | Domain | Operations | Exact degree |
|---|---|---:|---:|
| `integer12/integral_centered.json` | 12 unrestricted integers | 143 | 1200 |
| `integer12/rational_centered.json` | 12 unrestricted integers | 146 | 1184 |

Their whole-domain zero-set bijections are proved without excluding any
integer value of a denominator used only in the explanatory notation.
They use the separate six-port source34 tuple, not the positive-domain
tuple. The complete source34 recipe and every fixed coefficient are included.

## Logical and verification scope

For every main positive-domain polynomial `P`, composing the new ordinary
arithmetic proof with the precisely identified inherited source calibration
gives

> ZFC proves: P has no zero in ten strictly positive integers if and only
> if Con(ZFC).

The twelve-integer saturated equation and the controls have the corresponding assertion over
`Z^12`. Here `Con(ZFC)` uses the finite syntactic refutation calculus of
the pinned source. The construction does not assert that ZFC is consistent.

The native/controller/refutation calibration is inherited from ProveIt;
it is not reproved or newly formalized end to end in this packet. The new
ordinary proofs are written to be formalizable in ZFC. Executed programs
verify finite specifications, exact identities, degrees along test rays,
coefficient reconstruction, and transcription controls. Those computations
are not presented as proofs of unsolvability or substitutes for unbounded
semantic arguments. Global degree attainment is proved in the paper,
not inferred from specialization.

This is a repository-relative improvement in particular size/degree
tradeoffs. It does not establish a globally simplest consistency equation,
a new smallest variable count, or a lower-degree result than the repository's
separate quartic families.

## Reproduce

Run from the extracted directory:

```sh
python3 -B build.py --check
python3 -B verify.py
python3 -B -O verify.py
python3 -B integer12_saturated/build.py --check
python3 -B integer12_saturated/verify.py
python3 -B -O integer12_saturated/verify.py
python3 -B integer12/build.py --check
python3 -B integer12/verify.py --output /tmp/integer12-check.json
python3 -B alternative/relational_kernel.py
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

`build.py --check` compares every generated evaluator with its stored JSON
without modifying it. Omit `--check` to regenerate the equations. The main
verifier's checks remain active under `python -O`. The alternative local
kernel's diagnostic program should be run without `-O`.

For the ten-positive equations the JSON gate format is
`[register, operation, operand1, operand2]`, with
operations `+`, `-`, `*`. Inputs and fixed ports are named leaves; numerical
literals are integer leaves. The integer packets instead use typed nodes
(`variable`, `coefficient`, `integer`, `add`, `sub`, `mul`) whose arithmetic
operands are indices of earlier nodes, with a separate named-register map.
All supplied main evaluators have every gate,
input, and fixed port live.

## Contents

- `report.tex`, `report_parts/`, `report.pdf`: complete manuscript and proofs.
- `equations/`: four main polynomials and four earlier, dominated centering
  variants retained for comparison and reproducibility.
- `build.py`, `build_saturation.py`, `verify.py`: deterministic builders and
  independent specification checks.
- `coefficients/`: full BFS coefficient payloads and printed-seed recipe.
- `checks/`: verification receipts and exact integer-polynomial replay.
- `integer12_saturated/`: primary unrestricted-integer result, complete
  ordinary proof, independent semantic review, source proofs, coefficients,
  deterministic builder, and independent exact algebra verifier.
- `integer12/`: earlier unrestricted-integer controls, source proofs, coefficients,
  and a separate independent verifier.
- `alternative/`: an explicit seven-coordinate, degree-14 local equational
  inference kernel. It is a research component, not a complete Con(ZFC)
  polynomial and not a seven-variable consistency claim.
- `source/`: retained parent proofs, parent circuits, original tuple controls,
  upstream notices, and the inventory of incoming archives reviewed.
- `SOURCE_PINS.json`: pinned repository origins and source hashes.
- `RESULTS.json`: machine-readable domains, exact degrees, counts, and roles.
- `audits/`: a separate mathematical review, including its dependency boundary.
- `MANIFEST.json`: release-file sizes and SHA-256 digests.

Run `python3 -B check_manifest.py` before rebuilding files to verify every
listed release digest. Local LaTeX build outputs are not part of that list.

All repository comparisons and source citations are pinned to commit
`84e16e43092614bae262ca59651cb9d77e31a255` of
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/84e16e43092614bae262ca59651cb9d77e31a255).
See `source/README.md` for the exact inherited dependency boundary.
