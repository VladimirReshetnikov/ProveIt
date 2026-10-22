# Explicit Diophantine equations for Con(ZFC)

This package constructs one specific Diophantine equation, and a shorter
system of equations, whose lack of solutions is provably equivalent in ZFC
to Con(ZFC). It is prepared for incorporation into ProveIt.

**Start with [report.pdf](report.pdf)** or its editable [LaTeX source](report.tex).
The complete mathematical statement, coefficient recipe, soundness and
completeness arguments, exact-degree proofs, and limitations are in that report.

## Results

| Presentation | Domain and unknowns | Equations | Binary arithmetic operations | Exact degree |
|---|---|---:|---:|---:|
| Basic system | 15 positive integers | 6 | 61 = 34M + 27A | 60 maximum |
| Reduced-coefficient system | 15 positive integers | 6 | 62 = 34M + 28A | 46 maximum |
| P67 | 15 positive integers | 1 | 67 = 39M + 28A | 155 |
| P68 | 15 positive integers | 1 | 68 = 39M + 29A | 123 |
| Basic sum of squares | 15 positive integers | 1 | 78 | 120 |
| Reduced sum of squares | 15 positive integers | 1 | 79 | 92 |
| P67 with integer substitution | 41 unrestricted integers | 1 | 158 | 310 |
| P68 with integer substitution | 41 unrestricted integers | 1 | 159 | 246 |

M counts multiplication; A counts addition and subtraction. Multiplication by
a fixed numeral is charged. Fixed numerals, reuse, and equality comparisons
are free in this convention. The system and single-polynomial counts are
different interfaces. These are displayed-circuit upper bounds, not lower
bounds or claims of global optimality.

Every variant has a solution if and only if the exact blank K215 machine halts,
if and only if a finite ZFC refutation exists. The proof of that equivalence is
formalizable in ZFC. The arithmetic expression contains only ordinary
polynomial operations; no variable exponent, floor, population count,
bitwise operation, or implicit side constraint occurs in its evaluation.

## The exact coefficient contract

The main polynomial has four fixed integer coefficient ports:

- <code>Bm1</code> = B − 1;
- <code>Kconstant</code> = DC + B·DR;
- <code>MC</code>, the native content mask;
- <code>MF</code> = MF_native + B − 1, the **shifted source coefficient**.

They are four specific integers, not four additional unknowns. Their closed
finite formulas are in report Section 4 and
[data/k215_constants.json](data/k215_constants.json), with the exact local
window predicate in [code/blank_helical.py](code/blank_helical.py).
The recipe has no free parameters or unspecified machine index.

The coefficient height is enormous: B = 2^(5^67). Even B − 1 has 5^67 binary
digits. The recipe is exact, but the archive does not expand these integers
or enumerate all 1,420,903,358,357,108,792,377 local windows. The cost model
measures arithmetic description size and does not count coefficient bits.

## Mathematical and formal status

The delivered Diophantine bridge is a mathematical proof supported by
deterministic source reconstruction and finite audits. It is **not a new
Lean or Rocq formalization**. Existing K215 machine endpoints are identified
and included as source references; the full proof-assistant builds were not
rerun for this package.

No consistency proof, actual halting K215 computation, or actual full Pell
solution is supplied. Under Con(ZFC) the equations have no solutions.
The biconditional does not assume Con(ZFC). The report also states the
correct incompleteness qualification: mere consistency must not be
silently replaced by Sigma-1 soundness.

The construction specializes the native-window/Pell compiler to a fixed
blank computation. It removes the ordinary numerical-input interface,
uses K215's actual first transition for Start, and reserves the forbidden
selector for a locally allowed but globally impossible window.
It does not rely on global uniqueness of Start for soundness.

## Reproduce the checks

Python 3.10 or newer, standard library only:

    python3 -B code/verify_all.py --output verification_receipt.json

Without the output option, the bundle is left unchanged:

    python3 -B code/verify_all.py

The default is the full check, including independent direct enumeration
of all left/right pairs in the thirteen local-center categories.
The optional <code>--quick</code> omits only that direct enumeration.
See [code/README.md](code/README.md) for individual entry points.

The recorded [verification_receipt.json](verification_receipt.json) is a
full **PASS**. It checks source hashes; all 430 transition rows against the
Lean and Rocq tables; the finite bootstrap; 32 halting control presentations,
1,144 windows/overlaps, and 208 seams; the exact local-window cardinality;
all six delivered circuit packets; and the machine-to-coefficient bindings.

These finite checks supplement the general proofs. They do not prove the
unbounded reductions by exhaustive testing.

## Build the PDF

A standard TeX Live installation with pdfLaTeX is sufficient:

    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

Run a third time if LaTeX requests another pass for page references.
The supplied PDF has resolved references and has been rendered for layout
inspection. No shell escape or network access is needed.

The appendix tables are included as ordinary editable LaTeX. To regenerate
them from the JSON packets:

    python3 -B code/build_tables.py

## Directory map

| Path | Contents |
|---|---|
| report.tex, report.pdf | Main paper and compiled PDF |
| circuit.tex, cross_counts.tex | Generated LaTeX appendices |
| code/ | Circuit emitter, machine/tableau/count/constant auditors, audit wrapper |
| data/fixed_blank_67.json, fixed_blank_68.json | Complete positive-integer polynomial circuits |
| data/fixed_blank_system_61.json, fixed_blank_system_62.json | Complete six-equation systems and SOS finalizers |
| data/fixed_blank_67_over_Z41.json, fixed_blank_68_over_Z41.json | Complete unrestricted-integer circuits |
| data/k215_constants.json | Closed finite coefficient recipe and scalar layout |
| data/k215_transitions.json | Full 430-row machine plus source-identity evidence |
| data/upstream_manifest.json | Exact copied-source hashes and byte lengths |
| data/proof_dependencies.json | Scoped upstream proof dependencies |
| proofs/ | Additional arithmetic, Pell, tableau and calibration audit notes |
| upstream/ | Pinned mathematical/calibration dependencies with original repository paths |
| verification_receipt.json | Full reproducibility result |
| SHA256SUMS | Hashes of all distributed files other than this manifest itself |
| licenses/ | Upstream licenses |

The upstream collection is scoped. Historical progress headers and links
inside copied notes are not promises that all past research scripts are
included. No historical script is required or executed by the verifier.
The optional direct normalized-rank proof in the Pell audit is supported
by the additional copied affine-exponent note; the main paper uses the
audited generic strong-rank route.

## Repository integration and provenance

The original snapshot is:

    cdd582bec13f908df3711fa9e05d1ddac368a5db

Repository:
https://github.com/VladimirReshetnikov/ProveIt

The transition table SHA-256 is:

    fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090

The immediate 84-gate arithmetic parent SHA-256 is:

    8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf

A suitable destination is
<code>Computability/HilbertTenthProblem/Papers/research-wip/zfc-fixed-blank-67/</code>.
The archive is self-contained for its Python checks and PDF build, so it may
be copied there without changing the existing K215 verification tree.
The pinned upstream copies preserve the exact reviewed dependency versions.
New materials are offered for incorporation under the repository's MIT-0
license; copied material retains its existing notices and provenance.

