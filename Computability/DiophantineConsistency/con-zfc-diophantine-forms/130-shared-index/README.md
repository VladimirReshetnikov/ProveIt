# Explicit smaller Diophantine equations for ZFC consistency

Research packet prepared for Vladimir Reshetnikov's ProveIt project, 24 October
2026. The principal result is a **quartic in 241 nonnegative integer variables**.
The packet also supplies a denser 239-variable quartic and two different
improvements on the ten-positive-variable branch.

Start with **`report/report.pdf`**. Its LaTeX source is `report/report.tex`, with
three generated tables and the separate degree-246 section. Appendix A prints
**all 189 quadratic residuals** of the principal equation. The corresponding
JSON and the complete expanded polynomial are included, so the equation is a
finite literal object, not a request to choose a polynomial from DPRM.

## Results

| Equation | Domain | Variables | Exact degree | Additional size measures |
|---|---|---:|---:|---|
| **Principal direct quartic** | Nonnegative integers | **241** | **4** | **189 residuals; 30,058 monomials; height 85,187,728** |
| Dense direct companion | Nonnegative integers | 239 | 4 | 187 residuals; 387,494 monomials; height 269,805,528 |
| Quotient and absorbed padding | Strictly positive integers | 10 | 466 | **86 paid binary operations: 51 multiplications, 18 additions, 17 subtractions** |
| Weighted polynomial center | Strictly positive integers | 10 | **246** | 121 paid binary operations: 73 multiplications, 25 additions, 23 subtractions |
| Mechanical integer-domain lift | Unrestricted integers | 964 | 4 | 430 residuals; 33,083 monomials; height 85,187,969 |

For the principal equation, write `N={0,1,2,...}` and let

    P(z_0,...,z_240) = sum_(j=0)^188 Q_j(z)^2.

The ordinary mathematical proof, composed with the specifically identified
inherited C222/ZF/ZFC refutation calibration, establishes

    ZFC proves:  (there is no z in N^241 with P(z)=0) <=> Con(ZFC).

The same consistency equivalence holds for the other selected equations in
their stated domains. The direct quartics encode the numerical proof calculus
directly. They use neither a K215 simulation nor Jones's universal polynomial.
The positive companions retain their native/K215 calibration and four fixed
large coefficients; the complete original compact44 tuple and its finite
reconstruction data are supplied together.

These are ordinary mathematical reductions formalizable in ZFC. They do not
constitute a newly completed end-to-end Lean/Rocq proof, a new internal
object-ZFC proof term, a proof of consistency, or a proof of global minimality.
The retained logical-interface README explains precisely which calibration
files were inspected and which transitive formal dependencies were not rebuilt.

## Comparison and scope

The comparison snapshot is ProveIt commit
`f4d8db99e060339f3306a04d507c35bc1d0d68c5`. `SOURCE_SNAPSHOT.json` records the eight
incoming ZIP hashes and further retained source pins. The direct source has
its own complete ledger.

| Direct natural quartic | Variables | Quadratic rows | Collected monomials | Coefficient height |
|---|---:|---:|---:|---:|
| Incoming shared binomial | 319 | 254 | 10,283 | 86,842,335 |
| Incoming shared Pell bound | 261 | 194 | 31,679 | 85,566,955 |
| **This principal equation** | **241** | **189** | **30,058** | **85,187,728** |

Relative to the 261-variable parent, this saves 20 variables, five residuals,
1,621 monomials, and 379,227 units of coefficient height, at the same exact
degree. The dense 239-variable alternative deliberately trades much larger
support and height for two fewer variables.

The positive 86-operation equation improves arithmetic length over the
89-operation, degree-288 parent; its degree increases to 466. The degree-246
equation improves degree over the 97-operation, degree-254 sharp-center
parent; its arithmetic length increases to 121. No simultaneous improvement
in those two measures is claimed. The positive sharp quotient controls with
89/450 and 90/450 are included for diagnosis; 89/450 is dominated by the
pre-existing 89/288 equation.

Other repository branches already have fewer variables, different domains,
or different coefficient and degree costs. In particular, neither 241 nor
the mechanical 964-integer conversion is a global variable-count record.

## New mathematical steps

### 1. A shared index bound for two different certificate types

The common Pell bound is extended from exact powers to a mixed family of
exact-power and modular-numerator requests. Its raw frame includes **every
modular upper index**, not only the exact-power inputs. This is essential:
without it the squared index-error argument has an unproved size premise.

There are 25 distinct frame atoms and 15 independent seed indices. One full
indexed-Pell anchor, one aggregate bound on the ordinates, and one congruence
of the sum of squared errors certify all the seed indices. The raw scale
forces `A-1 > W^3`; hence the decoded sum of squared errors is both divisible
by `A-1` and strictly smaller than it, and must be zero.

### 2. A radix chosen after the actual CRT representatives

Use `q=N(S+1)^K`, where `S` is their sum, `N=B^K`, and `K=R`. At horizon
`t>=12`, the raw ceiling equations give

    V0+s=B*F,     V0=(F^2+1)^t>F^2,
    hence F<B and V0<=B*F<B^2<=N<q.

This justifies the first binomial digit before assuming either `F=t!` or
the intended binomial meaning of `B`. Once the factorial is decoded, the
remaining digit and precision bounds follow. Choosing the radix after the
representatives removes their former aggregate bound.

The inequality `V0<B^2`, the fixed-point factorial lemma, the shared-binomial
idea, and the original common-cap theorem all have explicit predecessors.
The new claim is their completed composition, enlarged frame, improved radix,
and materialized smaller polynomial, not invention of those earlier lemmas.

### 3. A quotient coordinate and a shorter carrier

On the scaled positive branch, every zero already forces `q^3 | Y`. Set
`Y=q^3*s` and cancel the resulting nonzero factor `q^12` from the norm.
The resulting 87-operation equation is in exact positive-zero bijection with
the parent. Absorbing `s` into the padding coordinate saves one more operation.
That last step requires a fresh sign proof; the identity involving
`n_old=n-s` alone would not preserve positivity. The supplied proof gives
both soundness and a fresh positive witness construction.

### 4. An exact polynomial center for the fused radical

On the direct positive branch, put `L=X+1`, `t=mu*Y`, and weight the fused
radical by `lambda=8*L^3`. Two exact polynomial quotient corrections give a
center `Gamma` with defect of weighted degree 34 rather than 42. Both center
and weighted root remain below `Q`, so the transport proof still applies.
An explicit nonzero coefficient proves the actual fixed polynomial's degree:

    [J^116*x^29*i^10*Y^57*eta^32*F^2] N = -7*2^14*beta^116.

The full 52-term center-defect certificate is supplied. Polynomial-part
centering already occurs elsewhere in the repository; the new result is
this application and the verified ten-positive-variable degree/cost point.

## File map

| Path | Purpose |
|---|---|
| `report/report.pdf` | Typeset report, complete principal residual appendix, both positive constructions |
| `report/*.tex` | Complete editable LaTeX source and generated tables |
| `direct/PROOF.md` | Direct soundness, completeness, witness order, and attribution |
| `direct/equations/principal241/natural/` | Literal residuals, full collected polynomial, restoration certificate |
| `direct/equations/dense239/` | Complete dense companion and its certificates |
| `direct/source/` | Frozen compiler closure, parent proofs, calibration interfaces, notices |
| `positive/` | Quotient equations, original coefficient tuple, finite recipe, proofs and checks |
| `center246/` | 121-row equation, exact 52-term defect, proofs and checks |
| `integer964/` | Explicit unrestricted-integer conversion of the principal quartic |
| `reviews/` | Independent reviews from separate agents in this AI-assisted research workflow |
| `verification/RELEASE_CHECKS.json` | Complete integrated verification receipt |
| `verification/REPORT_QA.json` | PDF compilation and visual-inspection record |
| `MANIFEST.json` | SHA-256 and size of every delivered file except the manifest itself |

“Independent review” here describes separate derivations and independently
written checks within the AI-assisted workflow. It is not external human
refereeing or a proof-assistant certification.

## Offline verification

Python 3.10 or newer, with its standard library, is sufficient for all
mathematical artifact checks. No network, repository checkout, hidden input,
or optional algebra system is required. From this packet's root:

```bash
python3 -B verify_all.py --rebuild --output /tmp/conzfc-release-checks.json
```

The verifier authenticates the manifest and source pins; checks all semantic,
affine, natural-restoration and expanded-polynomial certificates; checks the
literal report tables and integer-domain lift; checks all positive circuits
and the coherent constants; reconstructs the center equation in a temporary
directory; and compares selected rebuilds byte for byte. It does not modify
the frozen equation files. `--rebuild` additionally reconstructs both direct
quartic variants from the retained source. Without that flag it still checks
their complete certificates and coefficient lists.

The direct package's normal and optimized Python receipts include 225 exact
semantic checks, 428 affine restorations, all 108 principal natural
restorations, all collected coefficients, five rejected corruptions, and
fresh byte-identical rebuilds of both variants. The center package reports
151 checks, including exact symbolic center identities and 72 modular formula
comparisons. Point evaluations and finite-difference tests are transcription
checks, not proofs of an unbounded equivalence or of consistency.

To regenerate only the report tables and unrestricted-integer conversion:

```bash
python3 -B build_report_support.py
```

To compile the PDF with a standard LaTeX installation:

```bash
cd report
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

The mathematical JSON rebuilds are byte-exact. PDF byte identity is not
required across different TeX versions. After changing a source intentionally,
regenerate the manifest with `python3 -B package_release.py --manifest-only`.
Do not regenerate it merely to bypass an unexpected verification failure.

## JSON conventions

For direct polynomials, `[coefficient,[i,j,j]]` means
`coefficient*z_i*z_j^2`; an empty monomial list denotes the constant term.
The equation is the **sum of the individual residual squares**. It is not
the square of their sum. All coordinates are independently quantified in the
stated domain; coordinate names impose no extra conditions.

For positive circuits, each row `[name,op,left,right]` defines one paid binary
operation in topological order. String operands name earlier registers,
unknowns, or fixed coefficients; integer operands are literal constants.
The output register is the complete polynomial. Definitions contain no
variable exponent, division, square-root function, or external oracle.

## Remaining mathematical boundary

The unbounded new transformations have ordinary proofs of both directions.
The C222/ZF/ZFC calibration, indexed-Pell representation, and native-controller
calibration are explicitly inherited and attributed. Their retained source
files are not presented as a fresh rebuild of every formal dependency.
The equivalence does not establish either that the equations have a solution
or that they have none. A full end-to-end formal derivation remains separate
work; all literal equations, source pins, restoration certificates, and proof
boundaries needed to begin that integration are included.

New material follows the root license; imported files retain their original
notices and licenses. `licenses/native_sources/` preserves the native branch's
upstream notices.
