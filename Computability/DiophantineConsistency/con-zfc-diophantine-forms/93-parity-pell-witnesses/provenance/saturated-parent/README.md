# Quotient compression and a separated rational norm

Four explicit fixed-coefficient ordinary Diophantine polynomials, all over
**unrestricted integers**:

| Packet | Variables | Zero-set residuals | Exact degree | Binary arithmetic operations |
|---|---:|---:|---:|---:|
| `equations/integer23_degree10.json` | 23 | 11 | 10 | 131 |
| `equations/integer17_degree88.json` | 17 | 5 | 88 | 114 |
| `equations/integer16_degree192.json` | 16 | 4 | 192 | 134 |
| `equations/integer16_degree184.json` | 16 | 4; unit-product finalizer | 184 | 135 |

The strongest same-degree reduction is **19 to 17 unrestricted integer
variables at degree 88**. One quotient replaces two congruence witnesses;
a monic transport pivot removes another coordinate. A separated rational
norm then gives the 16-variable companions. The preferred degree-184
polynomial is G+N+GN, where G is a sum of three squares: its vanishing
forces (1+G)(1+N)=1 and hence G=N=0. The degree-192 sum-of-squares form
is retained as a control and saves one circuit operation. The degree-10 form combines
compatible residue orientation and Pell-root translations, improving the
incoming 24-variable degree-10 result.

`PROOF.md` gives complete proofs of the new reductions and states every
inherited semantic interface. `section.tex` is the article-ready LaTeX
presentation. Every polynomial packet contains its independent variable
list, ordered polynomial abbreviations, residuals, fully inlined versions,
and an exact leading-coefficient certificate. The first three equations
are sums of squares; the degree-184 equation has its explicit unit-product
formula in `polynomial_expression`. No abbreviation adds an unknown, and no
variable exponent or division occurs in a polynomial.

By composition with the identified ordinary native/compiler, signed Pell,
and syntactic-refutation calibration theorems, the absence of integer zeros
is provably equivalent in ZFC to Con(ZFC). This contribution does not
re-prove the whole inherited compiler or supply a new end-to-end Lean/Rocq
or encoded object-language ZFC certificate. It establishes the equivalence,
not either side. No global optimum or external priority claim is made.

## Reproduction

Python 3.10 or later and its standard library suffice. No network is used.

```sh
python3 build.py
python3 verify.py
python3 -O verify.py
python3 negative_controls.py
```

The normal and optimized verifiers reconstruct all four actual native
coefficients from the retained literal 943-tile recipe, verify both fixed
determinant powers, authenticate all retained sources, and check every
arithmetic parent-row restoration. The one restoration that uses
`c | f^2-1` is explicitly exposed as `R*(c*b-f^2+1)`; b is a proof witness
only and is not a polynomial coordinate. The unbounded proof of that
divisibility precedes use of the removed congruences, as explained in
Section 5 of the proof.

Exact homogeneous components certify the degrees. Exact free-term-algebra
comparison binds both literal inlined formulas and the binary DAGs.
Modular evaluations use actual fixed integers and are supplementary
diagnostics. Small rational-root tests supplement the universal norm and
descent proofs; they are not substitutes for them.

The six fixed ports are `beta,K0,MC,MF,cone_A,cone_B`. Their complete
minimal integer bytes total 615,883; gzip payloads and raw hashes are
included under `coefficients/`. They belong to one coherent source-34
tuple, and MF is already shifted. The payloads, not their hashes, define
the integer leaves. A reconstructible finite recipe is included.

The DAG counts include every live binary addition, subtraction, and
multiplication, including scalar arithmetic and squares. Fixed leaves and
register reuse are free. These counts are reproducible literal evaluator
sizes, not optimized minima or bit-complexity bounds.

## Files and provenance

- `equations/`: four complete polynomial packets.
- `circuits/`: literal shared binary evaluators.
- `METRICS.json`: exact variable, degree, residual, and operation counts.
- `certificates/`: finite verification and independent review receipts.
- `coefficients/`: all six actual fixed integers and the source recipe.
- `upstream/`: literal parent equations and nearest proof dependencies.
- `SOURCE_PINS.json`: reviewed commit, incoming archive hashes, and retained source hashes.
- `licenses/`: preserved licenses and source notices.

Reviewed repository: ProveIt commit
`c1a102936aca437e9999530a0111e6ddab56dc6d`, including all five incoming
archives present at that snapshot. This component's sources come from the
incoming structural round eleven and joint-guards packets plus the named
older repository files. `SOURCE_PINS.json` records complete paths and
hashes. The source-71 sparse arithmetic engine is retained with one
performance-only modification: binary exponentiation skips construction
of an unused final square. Its byte-exact original is also retained.

This directory is a self-contained component of the delivered research
archive. It introduces no repository writes or publication step.
