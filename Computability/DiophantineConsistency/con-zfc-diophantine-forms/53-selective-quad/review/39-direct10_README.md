# Direct quadratic coding: ten integer unknowns for Con(ZFC)

This package replaces the quartic source code of the current ten-integer
construction by a direct encoding of all 22 quadratic residuals. A finite B2
(Sidon) sequence gives short digit positions, and one binary carry test checks
all 22 target coefficients simultaneously.

**Result:** a completely specified polynomial in ten unrestricted integer
unknowns, with exact total degree **267,823,432**, evaluated by **786 binary
arithmetic operations**. There are **17 fixed leaves**. ZFC proves that this
polynomial has no integer zero if and only if Con(ZFC).

The improvement is relative to package 31 (`31-sun10`) at ProveIt commit
`22e75dd6b87b1b199bb08c778d7cf075ae5aae08`: the previous ten-integer equation has
exact degree 589,042,901,992,797,851,562,527,064 and 1,442 operations. The new degree
is smaller by a factor of about 2.20 × 10^18, with 45.49% fewer operations.
Unknown count stays at ten. No global optimality claim is made.

`report.pdf` is the complete article; `report.tex` is its editable LaTeX source.
It includes the parent system, all source and final polynomial definitions,
the proof in both directions, exact-degree certificates, and the second
coefficient improvement described below.

## Two complete fixed instances

The principal instance at the package root retains package 31's complete
native tuple. The separately bound `optional_compact/` instance combines
the direct quadratic source with a new exact bounded-checksum compiler.
Both have ten integer variables, degree 267,823,432, 786 operations and
17 nonliteral fixed leaves. They are distinct fixed polynomials.

| Quantity | Principal instance | Compact instance |
|---|---:|---:|
| Native base | 2^1,064,921 | 2^590,069 |
| Four native ports, raw bytes | 533,099 | 295,388 |
| Largest native port, bits | 1,070,004 | 592,884 |
| Source multiplier | 2^2,134,938 | 2^1,182,966 |

The compact tuple is also 41.6994% smaller in raw bytes than the previously
smallest complete tuple bound to the reviewed equations (package 36,
506,664 bytes). Its exact local word decoder, carry and synchronization
bounds, padding, actual-rank controller and ordinary proof are included in
`optional_compact/coefficients/PROOF.md`. All four ports and the subsequent
source bound are regenerated together. The principal instance allows the
source improvement to be assessed with the established coefficients.

## Mathematical specification

- `DIRECT_QUADRATIC_PROOF.md`: complete proof of the new source coding step,
  with the coefficient and range bounds needed by the inherited Lucas bridge.
- `generated/direct10.json`: complete division-free circuit; its only variable
  leaves are `f,g,h,k,l,w,x,y,z,m`, all ranging over Z.
- `generated/source_certificate.json`: exact weights, target exponents, residual
  order, coefficient bound, and source hash.
- `data/parent_quartic31.json`: the inherited 31-positive-variable, 22-quadratic
  parent, whose residuals are shifted to the nonnegative domain before coding.
- `data/INSTANCE.json`: exact binding of every fixed leaf. Coefficient recipes
  are embedded in the circuit, in the explicit port order `beta,K0,MC,MF`.
- `coefficients/`: the inherited complete `wang943-mixed-121x8801` native tuple,
  its proof, standard-library generator, literal K215-derived tile data and
  materialized binary coefficient ports.
- `upstream/`: exact inherited mathematical sources and the former circuit for
  comparison. References inside these historical source copies keep their
  original context and are not entry points for this package's build.

The displayed degree is the total degree of the polynomial, not a count of
expanded terms. The binary circuit uses 222 additions, 25 subtractions and 539
multiplications. Constant leaves and reuse are free; multiplication by fixed
numerals and all fixed powers are charged as binary gates.

## Reproduce

Python 3.11+ and its standard library suffice. From any directory:

```sh
python3 /path/to/this/package/reproduce.py
```

The driver reconstructs both complete coefficient tuples, rebuilds both
literal circuits, runs their independent audits, and checks:

1. all 528 distinct pair sums of the 32-element B2 set (including zero);
2. every simultaneous target coefficient as an exact multivariate polynomial;
3. the native raw-byte hashes and coefficient bit lengths;
4. strict coefficient bounds for the source base 2^2134938;
5. source-circuit transcription modulo three primes;
6. the exact 35-term identity for the final eight-factor norm;
7. a literal DAG comparison with the pinned package-31 downstream finalizer;
8. exact total degree by nonzero diagonal leading coefficients modulo primes;
9. small carry examples and deliberate missing-target/colliding-weight failures.

The authoritative receipt is `verification/RESULTS.json`. These finite checks
are not an end-to-end Lean or Rocq proof. The ordinary proof imports the existing
native compiler/K215 calibration and Sun's mathematical Lucas theorems.
The construction proves an equivalence; it does not prove Con(ZFC).

Additional independent receipts are
`verification/DIRECT10_INDEPENDENT_AUDIT.json` and
`optional_compact/verification/DIRECT10_COMPACT_INDEPENDENT_AUDIT.json`.
The compact compiler has its own independent full-integer audit. None of
these independent audit programs imports the candidate circuit generator.

Compile the article with a standard pdfLaTeX installation:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

`make verify` runs both instance reproductions; `make pdf` builds the article.
`INTEGRATION.md` describes the intended repository placement and provenance.

## Fixed coefficient integrity

The four native ports must be used as one complete tuple. The fourth (`MF`) is
already shifted by the native base minus one. The new source-base constant is
separate from that native base: `beta_source=2^2134938`. Every leaf is specified
by a fixed literal or a finite recipe. There is no unknown recursively enumerable
index and no unbounded coefficient search. Raw binary ports are little-endian.

## Attribution and novelty scope

The B2 finite-field construction is classical (Bose--Chowla). The modified
Lucas bridge is due to Sun; the coprime square merger, quintic merger and final
separating weights are inherited from ProveIt package 31. The new part here is
their combination with direct simultaneous quadratic coding: no quartic sum of
squares is formed, and exponential base-5 digit positions are replaced by the
explicit short B2 set. The entire downstream finalizer is literally identical
to package 31 after substituting the new source block.

New material was prepared with AI assistance for the ProveIt project. Original
licenses and notices are retained under `licenses/` and `coefficients/licenses/`.
The new code and prose are offered under the MIT-0 terms in `LICENSE`.

Primary references:

- R. C. Bose and S. Chowla, *Theorems in the additive theory of numbers*,
  Comment. Math. Helv. 37 (1962/63), 141–147,
  https://doi.org/10.1007/BF02566968.
- Z.-W. Sun, *Further results on Hilbert's Tenth Problem*, Sci. China Math. 64
  (2021), 281–306, https://arxiv.org/html/1704.03504v7.
- Z.-W. Sun, *Ten unknowns for Hilbert's tenth problem over the integers*,
  preprint (2026), https://arxiv.org/html/2609.01594v2.

