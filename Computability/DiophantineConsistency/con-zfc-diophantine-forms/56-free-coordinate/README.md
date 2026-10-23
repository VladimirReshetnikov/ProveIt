# Free Pell coordinates: a smaller equation for ZFC consistency

Research contribution for Vladimir Reshetnikov's ProveIt repository, dated
23 October 2026. Comparison snapshot:
`4b4349064a750ba6347293b55874a7f92abdd0db`.

## Main result

The primary polynomial has **nine strictly positive integer unknowns**, exact
total degree **4,686,812**, and a division-free evaluator with **560 live binary
operations**: 332 multiplications, 173 additions, and 55 subtractions.

Its absence of positive zeros is provably equivalent in ZFC to Con(ZFC), by
the new mathematical equivalence to the explicitly supplied 31-coordinate
source and the identified inherited ordinary compiler/calibration theorems.
The paper states and proves the new transformations and identifies the
imported results. No consistency assumption enters the construction.

Start with **`report/report.pdf`**. The complete LaTeX source is
**`report/report.tex`**, which includes **`short/section.tex`**.

| Construction | Domain | Exact degree | Binary operations |
|---|---|---:|---:|
| Incoming best-degree comparator | 9 positive | 7,344,328 | 738 |
| **New primary** | **9 positive** | **4,686,812** | **560** |
| New input-plus-one translation | 9 nonnegative | 4,686,812 | 567 |
| New original-H reference form | 9 positive | 4,686,812 | 562 |
| Incoming fewest-operation comparator | 9 positive | 15,502,748 | 548 |
| Incoming short comparator | 15 positive | 80 | 72 |
| **New Q54** | **15 positive** | **54** | **73** |
| **New Q46** | **15 positive** | **46** | **74** |
| Incoming lowest-degree short comparator | 15 positive | 44 | 75 |

The primary improves the best-degree incoming nine-variable point by 36.1846%
in degree and 24.1192% in operations. The incoming 66-operation/degree-157
fifteen-variable equation and 548-operation nine-variable equation retain
their distinct tradeoffs. These are improvements within the inspected
frontier, with no global-minimality or reduced-variable-count claim.

## New mathematical ideas

1. Make the old derived Pell coordinate C a free positive unknown. Recover
   its former lower bound from the norm's positive margin, using a small
   quotient translation to prove that margin before applying Jones's theorem.
2. Remove the leading binary block from the carry number and halve its block
   length. The exact population-count calculation adjusts the square
   divisibility threshold by the matching amount.
3. Evaluate twenty quadratic source rows through a shared homogeneous
   circuit, with the two low-target rows evaluated directly. This preserves
   all targets and source coefficients and avoids negative exponents.
4. Combine the ordinary gap minimum with a squared-modulus Pell quotient,
   and regroup a forced unit to obtain the two short alternatives.

The selective code, sharp Pell majorant, CRT absorption, original source
compiler, and calibrated machine endpoint are credited inherited results.
The new paper and component notices distinguish these contributions.

## Exact equation and files

The primary equation is specified by the literal straight-line program
`nine/generated/calibrated_absorbed_positive.json`. Its input order is

    b, g, h, s, w, C, i, j, n.

All inputs are strictly positive integers. Every intermediate register is
an abbreviation, not another existential variable. The output is one
polynomial with integer coefficients; no division, variable exponent, or
undetermined coefficient occurs.

The final norm is

    ([Theta^2 - Omega^2(a0+a1)]^2 - 4 Omega^4 a0 a1) = 0,

with every register defined in the report and `nine/PROOF.md`. The actual
15 fixed leaves, including the two fixed powers of two, are materialized
in `nine/fixed/`. The coherent four-port native coefficient tuple is in
`nine/coefficients/`. The coefficient builders and full native recipes are
also included under `short/coefficients31/`.

Main paths:

- `report/`: the complete paper, PDF and LaTeX.
- `nine/`: main polynomial, alternative domain/interface presentations,
  complete mathematical proof, fixed coefficients, generator, evaluator,
  degree certificates, independent algebraic auditor, and source receipts.
- `short/`: Q54 and Q46, their paper appendix, full proof, literal circuits,
  native coefficient builders, and exact leading-form audits.
- `review/`: independent internal mathematical review of the new arguments,
  manuscript, short constructions, and current baseline.
- `provenance/`: repository/archive pins and an aggregate reproducibility
  receipt.
- `SHA256SUMS.json`: hashes of every delivered file other than the manifest
  itself. Component manifests retain their original local paths and scope.

## Reproduce offline

Python 3.10 or newer and its standard library suffice for the numerical
construction and audits. No checkout, network access, symbolic-algebra
package, or proof assistant is required for these finite checks.

From the extracted archive root:

```sh
python3 verify_all.py
python3 -O verify_all.py
```

The driver checks the release hashes, copies the two components into a fresh
temporary directory, and verifies there. The main component rebuilds 30
files byte for byte, reconstructs every materialized fixed leaf, checks all
22 row identities and 71,808 isolation interactions, and performs exact
norm/degree checks. It also exercises 11,049 finite carry cases, 33 threshold
calibrations, and 1,200 modular evaluator comparisons. Its core is run both
normally and under optimized Python. Both short constructions are rebuilt
and audited in each Python mode, including their full leading homogeneous
forms. Assertions disabled by `-O` cannot bypass the checks.

These finite checks support the implementation and explicitly bounded
combinatorial claims. The universal solvability equivalence is proved by
the mathematical arguments and their named dependencies, not by sampled
evaluations.

A small modular evaluation of the actual primary polynomial is:

```sh
python3 nine/evaluate.py --modulus 1000003 1 1 1 1 1 1 1 1 1
```

The result is 2519. A residue calculation is not an integer-solution test.

To rebuild the paper, use a TeX installation with the packages named in its
preamble:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

Rebuilding a PDF can change its bytes because of TeX metadata. The release
hashes authenticate the delivered PDF; changing it requires refreshing that
manifest before rerunning the release hash check.

## Proof status and incorporation

This is an ordinary mathematical proof formalizable in ZFC with explicit
finite data and implementation audits. It is **not** a newly compiled
end-to-end Lean/Rocq proof, nor an exported derivation in the repository's
object-language ZFC calculus. The included Lean texts identify numerical
interfaces; their external import closure is not a standalone build here.
The existing checked nine-variable construction in the repository does not
automatically certify this new smaller literal circuit.

The most natural formalization order is the shifted-norm/free-coordinate
lemma, the two-block valuation identity, the literal source-evaluator
certificate, and then their composition with the existing compiler endpoint.
The report gives the exact hypotheses for each step.

The construction does not prove or disprove consistency, and no equivalence
for unrestricted integer inputs is asserted for a positive-domain polynomial.
Large coefficient heights and bit complexity are separate from binary
arithmetic circuit size. Preserve all inherited notices, licenses, and
coefficient/source bindings on incorporation.

The research and independent checks were performed within an AI-assisted
session; no external human peer review is represented.
