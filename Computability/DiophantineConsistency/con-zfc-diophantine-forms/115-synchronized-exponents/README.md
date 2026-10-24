# Synchronized exponent certificates for ZFC consistency

Research prepared for Vladimir Reshetnikov, 24 October 2026.
This package contains an explicit quartic in **358 nonnegative integer variables**,
an ordinary proof that ZFC proves its unsolvability equivalent to Con(ZFC),
and independent finite verification artifacts.

The construction was developed with AI assistance and separate arithmetic and
mathematical reviews. It is offered for repository review and incorporation;
it is not represented as a new Lean/Rocq formalization or a sealed
object-language ZFC proof.

## Main equation

Let `r[0], ..., r[274]` be the complete integer quadratic polynomials in
`direct/natural358/equation.json`. Define

    P358(X0,...,X357) = sum(r[j](X)^2 for j=0,...,274).

All 275 residuals are also printed, without omissions, in `report.pdf`
and `residuals.tex`. The collected polynomial, including every literal
integer coefficient, is in `direct/natural358/polynomial.json`.
The domain is **N = {0,1,2,...}**, not unrestricted integers.

The ordinary theorem is

    ZFC proves:
    [there is no X in N^358 with P358(X)=0] iff Con(ZFC).

The polynomial has exact degree 4, 8,229 nonzero collected monomials and
coefficient height **9,903,520,314,287,616,167,992,362,844** (94 bits).
The 361-variable companion has degree 4 and 6,759 monomials.
Every final variable occurs. All coefficient data are materialized; there
are no unspecified universal-polynomial parameters or variable-exponent
primitives in the equation.

## Contribution and comparison

The proof source is the repository's direct numerical **C222 calculus**,
calibrated to ZF and ZFC refutations. This construction does not encode a
K215 execution and does not use Jones's universal Diophantine expression.

The main change uses the same exponent

    e = 2^22 t,    t = t0+2,
    M0+1 = (t+1)^e,    H = (2+t+x+y+M0)^e.

The carrier keeps its meaning, while the larger admissible majorant H
allows both requests to share one indexed Pell pair. A common factorial
radius rho=(H!)^2 and a genuinely certified extra Pell index rho then let
the pairs at H+rho and t+rho be derived by the Pell addition law.
The auxiliary index has no arithmetic power request of its own, but its
entire index certificate is present.

The common square radius and squared-output factorial identity already
occur in the incoming Bootstrap package. The incoming centered factorial
identity and 395-variable quartic likewise predate this work. Those are
credited, not claimed as new. The new contribution is the combined
shared-exponent/extra-index construction and its literal 358-variable
projection. Novelty is relative to the inspected repository snapshot.

All following comparisons are quartics over nonnegative integers:

| Construction | Variables | Quadratic rows | Expanded terms | Height bits |
|---|---:|---:|---:|---:|
| Active candidate-output radii | 399 | 317 | 8,286 | 27 |
| Incoming centered factorials | 395 | 313 | 8,292 | 27 |
| Shared-square intermediate | 395 | 313 | 8,131 | 27 |
| New companion | 361 | 278 | 6,759 | 94 |
| **New main equation** | **358** | **275** | **8,229** | **94** |

The main result saves 37 variables (about 9.37%) relative to the inspected
395-variable incoming point, at a substantial coefficient-height cost.
The intermediate shared-square point is measured in the proof notes;
only the two final variants are included as main deliverables.
No globally simplest equation is claimed, and the repository's
smaller-variable, higher-degree equations remain distinct tradeoffs.

## The mathematical dependency order

1. Obtain the shared Pell-frame bound from the literal nonnegative atoms.
2. Recover the carrier and H first: their exponent is already positive.
3. Exclude T=0 from the literal base-T power modulus; thus rho=T^2>=1.
4. Recover the extra seed and all remaining power requests.
5. Use the uniform bound `binom(rho+n,j) <= (rho+1)^n` for rho,n>=1
   and 0<=j<=n. This recovers both factorial binomials before assuming
   either proposed output is a factorial.
6. Apply the squared-output fixed point, first to obtain T=H!, then
   to recover t! at the same radius.
7. Establish all remaining digit bounds from literal remainder inequalities;
   only then identify the CRT product, decode the local proof rows and
   apply the C222/refutation calibration.
8. Replay the certified natural-domain projections and take a sum of squares.

This ordering is part of the proof. It prevents circular use of factorial
or CRT-product meanings. The report supplies the unbounded arguments;
the finite controls do not replace them.

## File map

| Path | Content |
|---|---|
| `report.tex`, `report.pdf` | Full mathematical report and printed equation |
| `residuals.tex` | All 275 literal residuals |
| `direct/natural358/` | Main equation, projection certificate, complete expansion |
| `direct/natural361/` | Smaller-support companion and its certificate |
| `direct/source/` | Common 633-variable affine-contracted parent |
| `direct/raw_complete.json` | Complete 1,232-variable raw graph and semantic inventory |
| `direct/gate_ledger.json` | All raw variables, rows, affine and square-difference gates |
| `direct/interface.json` | Exact source coordinate bindings |
| `direct/CENSUS.json` | Machine-readable counts and heights |
| `direct/integer_companion.json` | Explicit composition for the integer-domain conversion |
| `code/construction.py` | Portable deterministic constructor for the direct artifacts |
| `code/verify.py` | Independent exact finite verifier |
| `code/check_latent_index.py` | Separately written raw identity/index checker |
| `code/check_arithmetic.py` | Exact finite arithmetic controls |
| `code/render_residuals.py` | Deterministic full LaTeX transcription |
| `code/evaluate.py` | Exact evaluator of either quartic or the integer companion |
| `checks/` | Normal and optimized verification receipts and arithmetic controls |
| `proofs/` | Inherited source proofs, comparison notes and independent ordinary reviews |
| `supplement/` | Five same-polynomial evaluator contractions, full data and own checker |
| `upstream/engine/` | Authenticated copied source engine and calibration dependencies |
| `SOURCE_PINS.json` | Repository, archive and comparison provenance |
| `SHA256SUMS` | SHA256 of every delivered file except the manifest itself |
| `LICENSE` | Repository license |

JSON residual terms have the format `[coefficient, [variable_indices...]]`.
For example, `[-3,[2,4]]` means `-3*X2*X4`; `[-6,[]]` is the constant
`-6`; `[1,[17,17]]` means `X17^2`. Monomials are ordinary commutative
products, and all indices are zero based. The polynomial is the **sum
of the squares of the residuals**, not the square of their sum.

## Reproduce and verify

Use Python 3.10 or later, with the standard library only.
Run these commands from this package's root:

```sh
python3 -B code/construction.py --check
python3 -B code/verify.py
python3 -B -O code/verify.py
python3 -B code/check_arithmetic.py
python3 -B code/render_residuals.py --check
python3 -B supplement/check.py
```

`construction.py --check` reconstructs the complete direct payload and
requires byte-for-byte equality, without changing it. Without `--check`,
it rewrites the direct generated artifacts.

The independent verifier does not import the generator or optimizer.
It checks all 599 affine eliminations, the majorant ledgers, every
subsequent nonnegative restoration, all final residuals and all expanded
coefficients. Two restoration formulas have negative collected coefficients
and are justified by supplied rational sums of squares. The checker also
rejects a modified final row after its target hash is updated.

The separately written checker verifies 22 actual power requests, seven
bases, 18 indexed pairs, all 15 seeds in the common divisibility product,
and three acyclic addition derivations. Normal and optimized runs pass.

The finite arithmetic controls cover 137,216 uniform binomial instances,
5,663 squared fixed-point candidates, 135 common-radius remainder
certificates and 111,881 radix exponent comparisons. They also retain
the counterexample showing why rho>=1 is required in the coefficient bound.
They are boundary and transcription checks, not a proof by finite sampling.

Compile the report with a standard TeX Live installation containing
amsmath, amsthm, mathtools, booktabs, longtable, lmodern, microtype,
xcolor, xurl, hyperref and fancyhdr:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

To evaluate a tuple stored in a JSON array:

```sh
python3 -B code/evaluate.py coordinates.json --variant natural358
python3 -B code/evaluate.py coordinates.json --variant natural361
python3 -B code/evaluate.py coordinates.json --variant integer1074
```

No numerical solution search is included or implied.

## An unrestricted integer equation

For integer a,b,c, set `g(a,b,c)=a^2+b^2+c(c+1)`.
The three-square theorem implies that g represents every nonnegative
integer, and it takes no negative values. Thus

    P358(g(a0,b0,c0), ..., g(a357,b357,c357)) = 0

is an explicit degree-eight equation in 1,074 unrestricted integer
unknowns with the same refutation/consistency equivalence.
The coordinate order is `(a0,b0,c0,a1,b1,c1,...)`.
Its composition file has every substitution explicitly recorded and binds
the parent by SHA256. The companion is not expanded into monomials.
It is a domain conversion and makes no improvement claim over the
repository's separate unrestricted-integer quartics.

## Exact evaluator supplement

These circuits are exact polynomial identities with their pinned parents:

| Positive variables | Parent operations | New operations | Exact degree |
|---|---:|---:|---:|
| 10 | 99 | 98 | 368 |
| 10 | 105 | 103 | 340 |
| 11 | 111 | 107 | 211 |
| 12 | 96 | 95 | 70 |
| 13 | 88 | 87 | 51 |

The incoming Bootstrap package already has a 110-operation evaluator for
the eleven-variable polynomial. The 107-operation result saves three
relative to that point, and four relative to its literal 111-operation parent.
Exact degrees are inherited by full polynomial identity; larger syntax-only
degree bounds are reported separately in the supplement.
The actual large coefficient payloads, their hashes and reconstruction
recipe, pinned parents, source notices and independent checker are included.

## Provenance and logical scope

Comparison snapshot:
`84e16e43092614bae262ca59651cb9d77e31a255` of
<https://github.com/VladimirReshetnikov/ProveIt>.
The copied engine comes from the pinned
`docs/incoming/ConZFC_407_888_Quartics_2026-10-24.zip` archive.
Its retained `source_commit` fields describe its older underlying
calculus/compiler provenance; they are not the date of this comparison.
Root and supplement source pins distinguish these layers.

The named inherited calibration interfaces are
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`.
The supplied copies establish provenance and support the ordinary
mathematical argument. They are not claimed to be a freshly rebuilt
transitive formal development of the new polynomial.

The equivalence is formalizable in ZFC. No proof of Con(ZFC) itself,
no decision of the final equation's solvability, no global optimum and
no worldwide priority claim is made.
