# Pell centers and fused bounds for Con(ZFC)

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026, with AI assistance.

This submission contains complete new ordinary arithmetic proofs and explicit
polynomials whose nonsolvability, in their stated domains, is provably
equivalent in ZFC to Con(ZFC), using the precisely identified inherited
logical calibrations. The report is **report/main.pdf**, with editable source
**report/main.tex** and all included TeX sections.

## Main results

| Equation | Domain | Variables | Exact degree | Additional size data |
| --- | --- | ---: | ---: | --- |
| `quartic212/reduced/equation.json` | Unrestricted integers | 212 | 4 | 152 squares, 21,556 collected monomials, coefficient height 6,432 |
| `quartic212/equation/equation.json` | Unrestricted integers | 212 | 4 | 152 squares, 5,290 collected monomials, height 277,420 |
| `projected/equations/integer106_degree32_linear.json` | Unrestricted integers | 106 | 32 | 47 squares, 1,830 operations |
| `projected/equations/integer82_degree16964_linear.json` | Unrestricted integers | 82 | 16,964 | 23 squares, 1,723 operations |
| `projected/equations/integer81_degree2097732_linear.json` | Unrestricted integers | 81 | 2,097,732 | 22 squares, 1,711 operations |
| `compact13/positive13_square.json` | Strictly positive integers | 13 | 174 | 69 operations |
| `compact13/positive13_oriented.json` | Strictly positive integers | 13 | 170 | 70 operations |
| `compact13/integer39_square.json` | Unrestricted integers | 39 | 348 | 160 operations |
| `compact13/integer39_oriented.json` | Unrestricted integers | 39 | 340 | 161 operations |

An operation is a live binary addition, subtraction, or multiplication;
integer constants are leaves. Circuit registers abbreviate polynomials and
are not quantified coordinates. Exact expanded coefficient heights are
reported only where the polynomial has actually been collected. The projected
graphs' largest literal is 1,099,511,627,780; that number is not an expanded
coefficient-height claim. The compact tuple occupies 94,689 raw bytes and is
fully reconstructed from its retained finite seed and recipe.

The principal quartic is literally

    P(x0,...,x211) = sum(Rj(x0,...,x211)^2 for j=0,...,151) = 0.

All 152 residuals appear in the report appendix and in both machine-readable
and plain-text files. The expanded polynomial is also included. Every input
of this equation ranges over all integers.

## The new ideas

**A polynomial Pell center.** Replace the old large-multiplier growth block by

    t=64+4z^2, S=t^2, T=S^2, Z=TF,
    X^2-Z^2-2ZF=1, F=T(2u+1).

The center is t^4+1. Divisibility of the Pell ordinate forces its positive
index to be at least t^4, giving the required label-separation growth. A
cofinal residue construction ensures binom(F+t,t) is odd. It is essential
to prove that latter compatibility; a growth estimate alone would not
establish completeness. The small-coefficient version then uses 465
reversible integral residual-row operations.

**One certificate for two bounds.** If U,V are squares, E>=1 and R>=0,

    UV-UE-VR-1 = a^2+b^2+c(c+1)

forces U,V>0, V>E and U>R. In the canonical refutation construction the
relative deficits total less than 71/128, so this stronger certificate
always exists. Replacing two private ternary certificates by one removes
three unrestricted integer coordinates. Combining this with the new linear
Pell-orientation numerator saves 65 operations in the matched 85-to-82
profile without increasing its degree.

**A second Pell root carries a native quotient.** The exact congruence
psi_S(2j+1)=(-1)^j modulo 4S^2 permits a signed polynomial carrier
`y=1+4[h(m-LB)-B]`. It authenticates the deleted quotient's integrality
and positivity before native rank recovery. The equation has 13 positive
coordinates; the separate 39-integer lift uses the standard ternary
positive parametrization. Their domains must not be conflated.

## Compare honestly

The comparison revision is
`b42c796d1f5de9912a576bc2fd77b778ae7402bf`. The incoming 210-variable
quartic still has fewer variables than the new 212-variable construction,
but coefficient height 2^40. Other incoming 215-variable quartics have
height as low as 2,304. The new sparse and small-coefficient quartics are
different tradeoffs. The 82-variable direct equation improves its matched
85-variable degree-16,964 predecessor, not the global variable-count frontier.

The 13-positive-variable compact equation removes one coordinate from its
14-positive-variable, 65-operation, degree-150 parent, with four extra
operations and a higher degree. Its standard integer lift improves the
parent's 42 variables / 163 operations to 39 / 160, at degree 348 rather
than 300. Global minimality and worldwide priority are not established.

## Reproduce the finite checks

Python 3.12 was used; the code uses only the standard library. No network or
root search is required.

```sh
python3 -B verify.py --checksums
python3 -B -O verify.py --checksums
```

The top-level checker authenticates every declared artifact, independently
checks the quartic graft and its row ledger, parses the printed appendix,
replays the projected immediate parent, checks the orientation and fused
guards, reconstructs the projected graphs byte for byte, and verifies the
compact formulas, degrees, integer lifts and complete fixed constants.
Checks remain active with Python assertions disabled.

Detailed actual receipts are in `verification/` and in the component
verification folders. `reviews/INDEPENDENT_ARITHMETIC_REVIEW.md` records
the separate mathematical review. To evaluate a supplied tuple, use the
component's `evaluate.py`; each supports an optional modular diagnostic.
Such a diagnostic is not a root of the consistency equation.

To reconstruct the raw quartic into a separate directory:

```sh
python3 quartic212/build.py --source quartic212/source210.json --output /tmp/conzfc212-raw
```

The small-coefficient rows are reproduced exactly by the elementary ledger
in `quartic212/reduced/basis_certificate.json`. The optional
`quartic212/reduce_basis.py` is the exact greedy search that found that
ledger. The projected component has `rebuild_all.py`; the compact component
has `build.py` and `reconstruct_coefficients.py`. Run compact graph
reconstruction in a working copy because its four JSON targets are written.

To rebuild the PDF from the package root:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

## Proof boundary

The direct constructions retain the C222/ZF/ZFC endpoints
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`, together with the
square-shell recoding and arithmetic extraction theorems. The compact
construction retains the exact admissible942 native/compiler calibration.
The report and component proofs identify these dependencies and distinguish
them from the new results.

The new ordinary proofs are formalizable in ZFC. No fresh end-to-end
Lean/Rocq build or sealed object-language proof is claimed. Finite artifact
checks establish exact algebra, not unbounded logical equivalence on their
own. Neither consistency, inconsistency, nor actual solvability is asserted.
The unrestricted statement relates internally coded integers and finite
derivations, including in nonstandard models; it does not assume an external
standardness restriction.

Suggested repository placement and precise claim wording are in
`INTEGRATION.md`. Original source notices and licenses are retained.
