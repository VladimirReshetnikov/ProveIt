# Calibrated determinant guards for Diophantine ZFC consistency

Prepared for Vladimir Reshetnikov and ProveIt, 23 October 2026.

**Main result: an explicit quartic in 38 unrestricted integer unknowns whose
absence of integer zeros is provably equivalent in ZFC to `Con(ZFC)`.**
Exact polynomial eliminations also give degree 6 in 32 integers and degree 8
in 27 integers. Two separate positive-variable companions improve degree and
arithmetic cost at 12 and 9 unknowns.

The mathematical article is `report.pdf`; its complete LaTeX source is
`report.tex`, with the two included sections under `positive12/` and
`nine_positive/`. All fixed coefficient values, finite construction recipes,
polynomial packets, exact checkers, retained source proofs and notices are
included. No network is needed for mathematical replay.

## Results and comparison

The comparison snapshot is ProveIt commit
`9cca523d9f27ad39d52993f4065cbd7e58f8bdd4`, including packages 60–67.

| Equation | Witness domain | Unknowns | Exact degree | Binary operations | Inspected predecessor |
|---|---|---:|---:|---:|---|
| `Q38` | all integers | **38** | **4** | not optimized | package 64: 41 integers, degree 4 |
| `S32` | all integers | **32** | **6** | not optimized | package 62: 35 integers, degree 6 |
| `O27` | all integers | **27** | **8** | not optimized | package 62: 30 integers, degree 8 |
| `P12` | strictly positive integers | 12 | **110** | **102** | package 61: degree 118, 104 operations |
| `F9` | strictly positive integers | 9 | **1,379,730** | **478** | package 67: degree 1,494,006, 487 operations |
| `F9_natural` | nonnegative integers | 9 | **1,379,730** | **485** | explicit domain translation |

The three integer results each save three variables at their fixed degree.
The nine-positive result reduces the lowest inspected degree by 114,276
(about 7.65%). It does not improve package 62's separate 453-operation
nine-positive entry at a higher degree. No ten-integer variable-count
improvement, global optimum, or worldwide priority claim is made.

Operation counts charge each live binary `+`, `-` and `*`, including a
squaring or multiplication by a fixed numeral; constants and register reuse
are free. They measure arithmetic graph size, not bit complexity. Fixed
coefficient ports are numerals, never existential unknowns.

## The structural contribution

The previous quartic imposed the two common-sign conditions `F*alpha > 0`
and `F*C > 0` with two independent triples of integer witnesses. Here

```text
q = beta*J + 1,
C = q - F - alpha,
Pos(x,y,z) = 1 + x*x + y*y + z*(z+1).
```

Every value of `Pos` is positive, and every positive integer is a value of
`Pos`, by the three-square theorem applied to `4n-3`.

The new single quadratic row is

```text
U = 2^1113 * F,
V = 2^666104 * C,
U*V - (q-U-V)^2 = Pos(t1,t2,t3).
```

This saves one triple. Its soundness covers **arbitrary signed integer
assignments**. A positive left side forces `U,V` to have the same nonzero
sign, and

```text
|q-U-V| < sqrt(|U*V|) <= (|U|+|V|)/2.
```

Therefore `q,F,C` have the same sign and
`|q| > (|U|+|V|)/2 >= |F|+|C|`; hence `alpha=q-F-C` has that sign as well.
Both old guards can be restored.

Completeness uses the native compiler's **canonical witnesses**, whose
leading digits are already controlled. For the authentic whole source-34
tuple, exact support and carry estimates prove, uniformly in the accepting
computation's size and permitted rank tuning,

```text
q/2 <= U < 4q/5,
q/2 <= V < 3q/5,
U*V - (q-U-V)^2 > 3q^2/25 > 0.
```

The new guard therefore preserves existence of a zero. It need not be true
of every old zero on the same old coordinates. This distinction is essential:
soundness restores old witnesses; completeness regenerates canonical ones.

`Q38` is the sum of squares of 25 quadratic residuals. Its degree is exactly
4 because its `tau^4` coefficient is 1. The sextic first centers one Pell
coordinate, then eliminates six monic registers. The octic eliminates eleven
monic registers. Complete inverse maps restore every original quartic row;
the exact degree certificates are `[r^2*c^4]S32=4` and `[a^4*f^4]O27=1`.

## Literal equations and coefficients

The authoritative integer definitions are:

- `integer_forms/quartic38.json`: all 38 unknowns and all 25 residuals.
- `integer_forms/sextic32.json`: all 32 unknowns, 19 residuals, full inverse.
- `integer_forms/octic27.json`: all 27 unknowns, 14 residuals, full inverse.
- `integer_forms/*_expanded.json`: exact sparse expansions with coefficient
  ports left symbolic. These contain 628, 586 and 707 symbolic terms.
- `coefficients/NEW_BINDING.json`: all six fixed integer values by byte
  binding and finite recipe. The four native ports are the complete
  `mixed-parity-unrounded-1064921` tuple; the extra two are powers of two.

`MF` is already shifted by the native `B-1`. It must not be shifted again.
The native tuple must be replaced as a whole, not mixed with ports from a
different compiler layout. In particular, the nine-positive companion's
original31 tuple has the same radix exponent as source34 but different
remaining ports. The twelve-positive companion uses the whole compact44
tuple with radix exponent 590,069.

Every exponent in these specifications is a fixed nonnegative integer.
All registers in the positive-variable graphs are polynomial abbreviations.
Thus the artifacts specify ordinary integer-coefficient polynomials, with
no variable exponentiation, hidden free parameters, or unresolved search.

There is a coefficient-size tradeoff. The main six numerals occupy 615,883
bytes uncompressed: 532,479 inherited bytes plus 83,404 bytes for the two
power-of-two leaves. Their compressed payloads are supplied. The exact pure
`J^4` coefficient of `Q38` is

```text
beta^4*(2^666104-1)^4 + beta^4 + beta^2*(beta-MF)^2.
```

It has 6,924,100 bits. This is a lower bound on maximum expanded coefficient
height; it is not asserted to be the maximum. A shorter witness list does
not automatically mean a shorter fully expanded numerical polynomial.

## Proof status

For each supplied equation `P` with its stated domain `D`, the mathematical
claim is

```text
ZFC proves: (there is no x in D with P(x)=0) iff Con(ZFC).
```

The proof goes through the existence equivalence with a finite syntactic
ZFC refutation and then negates both sides. It neither assumes nor proves
ZFC's consistency. The consistency predicate is the repository's fixed
refutation predicate; it is not replaced by semantic soundness.

The new determinant and elimination arguments are supplied as unbounded
ordinary mathematical proofs. They compose with the retained native
compiler, Pell classification/rank, and K215/refutation calibration proofs.
The positive companions likewise state their inherited interfaces and give
the new unbounded reductions. This is a proposed research contribution with
internal AI-assisted review, **not external peer review**.

The optimized native bridge's formal calibration in Lean, and an exported
derivation in the repository's object-language ZFC calculus, remain open
work. No newly compiled end-to-end Lean/Rocq certificate is included. The
active repository's closed generic consistency equation remains a separate
formal baseline. See the article's proof-status section and the retained
`upstream/ACTIVE_FORMALIZATION_README.md`.

Finite tests do not establish the unbounded semantic reductions. They check
the actual constants, support/carry hypotheses, exact polynomial identities,
inverse maps, liveness, degrees, graph counts and coefficient bindings.
Bounded sign boxes and modular examples are explicitly supplementary
transcription diagnostics.

## Reproduce the results

From this directory, with Python 3.10 or newer:

```bash
python3 verify_all.py
python3 -O verify_all.py
```

The verification uses only the Python standard library. Both modes rebuild
all three complete coefficient tuples and every new polynomial graph. The
normal and optimized receipts are under `certificates/`. No acceptance
check in the new verifiers relies on a removable Python assertion.

`check_integer_independent.py` uses a separately written AST parser and
sparse polynomial engine. It imports neither the primary integer engine nor
the main generator, and independently reconstructs all six main constants.
Written mathematical reviews are under `reviews/`.

To rebuild the PDF, use a TeX Live installation with the packages named in
`report.tex`:

```bash
python3 build_report.py
```

`MANIFEST.sha256` records the delivered file bytes. Verification regenerates
receipts and compressed payloads; different Python/zlib versions can change
gzip container bytes while leaving the authoritative decompressed integer
bytes identical. The mathematical replay always checks those raw values.
The PDF build is separate from the finite mathematical replay.

## Integration and provenance

This directory can be added as a new research package under
`Computability/DiophantineConsistency/con-zfc-diophantine-forms/`.
Choose its number at incorporation time. It does not modify the active
formally checked equation.

`SOURCE_PINS.json` records the exact upstream main-source identities.
Each positive companion has its own `PROVENANCE.json`. Original imported
proof texts retain their source context and may name paths in the original
package; the current definitions and paths in this README and the new article
are authoritative for this package. `NOTICE.md`, `LICENSE` and the retained
component licenses identify attribution and redistribution terms.

The strongest new idea is the calibrated determinant guard. The nine-positive
result is a concrete composition of compatible existing improvements;
the twelve-positive result combines an adaptive carrier with a new centered
norm. The article also records why the investigated direct-provability route
was not promoted as a competitive small equation.
