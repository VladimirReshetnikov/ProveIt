# Valuation separation and signed certificates for Con(ZFC)

This contribution gives two exact reductions, with editable TeX, a compiled report,
literal equations, generators, independent checks, and pinned inherited proofs.

**Main result:** a polynomial in **12 unrestricted integer variables**, of exact
degree **2,400**, evaluated by **215** live binary arithmetic operations. Its
**2,912-degree / 209-operation** companion offers a different tradeoff.

**Direct alternative:** a fully expanded quartic in **1,190 unrestricted integer
variables**, with **26,411 monomials** and coefficient height **83,900,628**.
It encodes the calibrated numerical calculus C222 directly; this route uses
neither K215 nor Jones's universal polynomial.

For each equation the ordinary proof, composed with the explicitly identified
inherited calibration, proves in ZFC that having no integer solution is
equivalent to Con(ZFC). This does not prove consistency, inconsistency, or
global minimality. The packet does not supply a new complete proof-assistant
derivation of the internal ZFC biconditional.

## Read first

- `report/report.pdf`: complete article.
- `report/report.tex` and its supporting inputs: editable article and coefficient recipe.
- `integer12/proofs/PRIME_TWELVE.md`: independent-readable new arithmetic proof.
- `direct/PROOF.md`: exact domain conversion and signed projection proof.
- `METRICS.json`: machine-readable endpoint metrics.
- `SOURCE_PINS.json`: exact inspected repository commit and incoming archive hashes.

All comparisons use ProveIt commit
`85ae4070019efd66ea3e58e9a67d287528094e8b`, including the recent incoming
archives. Their upstream filenames dated 2026-10-24 are retained verbatim;
this report is dated 23 October 2026 in Pacific time.

## The equations

| File | Domain | Variables | Degree | Further metric |
| --- | --- | ---: | ---: | --- |
| `integer12/equations/prime_separated12_degree2400.json` | integers | 12 | 2400 | 215 operations |
| `integer12/equations/prime_separated12_degree2912.json` | integers | 12 | 2912 | 209 operations |
| `direct/output/expanded_polynomial.json` | integers | 1190 | 4 | 26411 monomials |
| `direct/input/expanded_polynomial.json` | integers | 1224 | 4 | 23590 monomials |
| `supplemental/ordinary98/ordinary12_98.json` | positive integers | 12 | 70 | 98 operations |

The 12-integer circuits have only integer leaves, variables, and binary
addition, subtraction, and multiplication. Their six coefficient leaves are
fixed authentic integers, with actual payloads and a bounded reconstruction
recipe under `integer12/inherited/root_fusion/`. The compact norm notation
in the article is just a readable definition of these ordinary polynomials.

The direct quartic is also supplied as the sum of squares of 600 literal
quadratic residuals in `direct/output/equation.json`.
The 1224-variable checkpoint uses fewer monomials and is retained as a
useful tradeoff.

## What is new

1. The prime-3 congruences already present in the Pell certificate separate
   the five square-root terms. Constant weights 1, 3, 9, 27 replace the
   prior growing polynomial weights.
2. An adjacent-Pell descent proves an extracted rational auxiliary root
   is integral, allowing a lower-degree denominator-cleared norm.
3. The classical intersective carrier (x^2+3)(x^3-19) has a remainder whose
   odd coefficient is a unit modulo 3, so the previous monotonicity
   requirement is unnecessary.
4. A finite sign-inference certificate reduces the direct natural-domain
   guards to 234; 34 reversible signed monic substitutions then reduce the
   integer quartic to 1190 coordinates.

These are explicit improvements relative to the inspected inputs. The classical
carrier and general norm, Pell, three-square and substitution tools are not
claimed as new mathematics. There is no worldwide-priority claim.

The supplemental 98-operation evaluator is a smaller, separate optimization:
it gives **exactly the same** degree-70 positive polynomial as its 100-operation
parent. Its compact44 coefficient tuple is preserved separately and must not
be substituted into the main source-34 circuit.

## Reproduce

Python 3.10+ and the standard library suffice:

```sh
python3 verify.py
python3 -O verify.py
```

To retain a new receipt:

```sh
python3 verify.py --receipt /absolute/path/release-check.json
```

The root verifier checks the manifest, regenerates both main circuits,
compares every coefficient of the generic 20349-term norm, authenticates
the native coefficient payloads, independently checks the main arithmetic
front ends, regenerates and independently verifies the direct artifacts,
and checks the supplemental exact identity. Finite checks do not establish
the inherited unbounded compiler/calculus theorems anew.

For the entire retained synchronized parent replay, optionally run:

```sh
python3 direct/upstream/synchronized/verify.py
```

Build the PDF from the `report/` directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

Normal and optimized release checks, independent review notes, and PDF review
are retained under `verification/` and `reviews/`. The original dependency
notices and license texts remain in their respective directories.

## Suggested repository placement

The archive root can be placed under a new research directory such as
`Computability/DiophantineConsistency/research/valuation-signed-certificates/`.
No repository file is overwritten by this package. The root README and
report identify exactly which incoming constructions it improves.

The article and equations should be reviewed as an ordinary mathematical
contribution with explicit imported dependencies. In particular, see
`integer12/inherited/root_fusion/provenance/CALIBRATION_STATUS.md` for the
difference between the ordinary equivalence and the project's still
separate encoded object-language formalization target.

