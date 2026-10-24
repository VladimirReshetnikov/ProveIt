# Prime separation for Diophantine ZFC consistency

**Primary result:** an explicit ordinary polynomial in **13 unrestricted integer
variables**, of **exact total degree 1392**, with a **205-operation** shared
arithmetic evaluator. Composing the new ordinary mathematical proof with the
identified ProveIt native-compiler and refutation-calibration theorems gives

\[
\mathsf{ZFC}\vdash
\bigl(\neg\exists\mathbf x\in\mathbb Z^{13}\;P_{13}(\mathbf x)=0\bigr)
\longleftrightarrow\operatorname{Con}(\mathsf{ZFC}).
\]

Prepared for Vladimir Reshetnikov and incorporation in ProveIt. New research
and internal reviews are AI-assisted. Reviewed repository snapshot:
`cfbf118b4ad9b2c651fe96b571d9415261766328`, including the ten relevant incoming
archives present at that snapshot. No claim of global minimality, historical
priority, or new end-to-end proof-assistant verification is made.

## Start here

- `report.pdf` is the 19-page article; `report.tex` is its standalone source.
- `new_integer_compact/five_root_integer13_compact.json` is the primary literal
  polynomial, as a division-free arithmetic circuit with fixed integer leaves.
- `new_integer_compression/PROOF.md` is an additional detailed proof, including
  the restoration maps, canonical completeness, and degree analysis.
- `new_integer_compression/coefficients/` binds all six exact coefficient
  integers. The other symbols in the formula are abbreviations, not variables.
- `verify_all.py` replays the finite construction and algebra certificates.

## The new arithmetic idea

Four weighted Pell roots have distinct orders at the fixed prime 3: 2, 1, 0,
and a negative order. A finite sign-product argument prevents cancellation
within any subset. A rational signed sum therefore forces every root to be
rational. Monic square equations make three roots integral, and an elementary
adjacent-coefficient Pell descent makes the fourth integral. A fifth radical
incorporates a positivity witness at a still higher order. The syntactic
substitution `c = 2*c1 + 1` establishes the required nondegeneracy before that
guard is recovered, avoiding circular reasoning.

The proof retains the source-34 native encoding and the inherited K215
calibration. Its new root merger does not use the Jones or Sun small-variable
finalizer. The exact dependency boundary is in article Section 3 and in the
preserved inherited proofs.

## Four explicit polynomials

All four domains are unrestricted integers. A binary addition, subtraction,
or multiplication counts as one operation, including multiplication by a
fixed small integer and squaring. Reusing an existing result is free. Fixed
coefficient leaves are precomputed; this is an arithmetic-operation count,
not a bit-complexity estimate.

| Variables | Exact total degree | Operations | Add | Subtract | Multiply | Compact file prefix |
|---:|---:|---:|---:|---:|---:|---|
| **13** | **1392** | **205** | 47 | 28 | 130 | `five_root_integer13` |
| 14 | 696 | 151 | 38 | 23 | 90 | `four_root_integer14` |
| 15 | 244 | 137 | 33 | 24 | 80 | `three_root_integer15` |
| 16 | 108 | 132 | 33 | 24 | 75 | `fixed3_crt_integer16` |

The inspected source-67 thirteen-integer construction has degree 10,461,744
and 519 operations. Thus the primary construction gives a substantial
improvement at that variable count. Existing ten-integer equations use fewer
variables; nine-positive equations have a different domain. No ordering of
all competing notions of simplicity is assumed.

The `propagated_degree_upper_bound` in a compact packet is a deliberately
naive gate-by-gate bound. Cancellations make it larger than the exact degree
in three cases. Use `exact_total_degree`, the mathematical upper-bound proof,
and `DEGREE_LOWER_CERTIFICATES.json` for the certified degree.

## Coefficients and exact interpretation

The fixed ports are `beta`, `K0`, `MC`, `MF`, `cone_A`, and `cone_B`.
They are one coherent native tuple and its calibrated determinant scales:

```
beta   = 2^1064921 - 1
cone_A = 2^1113
cone_B = 2^666104
```

`K0`, `MC`, and `MF` are supplied literally as bytes and reproduced by the
finite recipe in `coefficient_recipe/`. **MF is already shifted by beta.**
The recipe verifies the literal 430-transition machine, all 943 tiles,
finite convolution constraints, carry bounds, and controller arithmetic.
It does not search for a refutation or simulate an unbounded computation.

Each `.bin.gz` decompresses to a minimal unsigned little-endian integer:
byte sequence `b[0],...,b[n-1]` denotes the sum of `b[i]*256^i`.
The six raw encodings total 615,883 bytes; their compressed payloads total
10,607 bytes. This is not a claim that the expanded polynomial has small
coefficients. Full raw and compressed hashes are in `BINDING.json`.

For a circuit packet, `v:name` reads a quantified input, `c:name` reads a
fixed port, and `n:k` is the literal integer k. Process `fixed_recipes` and
then `nodes` in order, applying each binary `add`, `sub`, or `mul` to its
two references. The value referenced by `output` is the polynomial. All
nodes and constants are finite. The separate `polynomial_definitions`
field documents the expressions; the independent primary-formula checker
binds those expressions to the actual literal gates exactly.

## Reproduce the verification

Requires Python 3.10 or later, with its standard library only. From the
extracted package directory run:

```sh
python3 verify_all.py
python3 -O verify_all.py
```

The second command demonstrates that acceptance checks remain active when
Python assertions are disabled. A new `VERIFICATION_LAST_RUN.json` is written;
the delivered optimized-mode `VERIFICATION.json` and normal-mode
`VERIFICATION_NORMAL.json` are retained unchanged. The script checks:

1. All six coefficient payloads, both hash formats, and a complete rebuild
   of the four native ports from the literal machine and tile data.
2. Byte-identical regeneration of all eight dense and compact circuit files;
   topology, variable liveness, absence of hidden inputs, and operation counts.
3. Exact universal three-root and four-root norm identities in integer
   polynomial rings, and the exact quadratic-algebra identities used for
   the fifth root.
4. Independent exact agreement of the actual 205 gates with the separately
   written primary formula; this check does not import either circuit builder.
5. Acyclic polynomial scope of all explanatory abbreviations; diagnostic
   modular comparisons of companion implementations.
6. Independent full univariate specializations and exact nonzero leading
   coefficients modulo 65521 for all four degree certificates. The upper
   bounds are proved symbolically in the article.
7. The ancillary ten-integer optimizations and the package checksum manifest.

Finite arithmetic verification does not establish consistency or replace
the unbounded soundness/completeness proof. The ordinary proof and its
inherited mathematical dependencies remain essential.

To rebuild the article, use an ordinary TeX Live installation:

```sh
pdflatex -halt-on-error report.tex
pdflatex -halt-on-error report.tex
```

## Ancillary ten-integer improvements

`ten_integer/` applies three exact local arithmetic identities to four
existing ten-integer polynomials. It preserves their zero sets because it
preserves the entire polynomials. The operation counts change from
480/484/487/521 to **477/481/484/518** respectively; the degrees remain
1,245,324 / 1,179,788 / 1,114,252 / 1,081,125. These are modest evaluator
improvements to inherited constructions, separate from the new prime
separation theorem. Their source files, coefficient data, transformations,
proofs, and verification are preserved in that directory.

## Provenance and integration

`SOURCE_PINS.json` records the reviewed snapshot, incoming-archive identities,
and copied source material. `inherited/PARENT_SOURCE_PROVENANCE.json` and
the component ledgers preserve the earlier source pins. Some original
upstream documents retain paths relative to their original packages; their
origin is explained in `inherited/README.md`. The active scripts in this
package use only bundled paths.

`LICENSE`, `NOTICE.md`, and `licenses/` record new-work and inherited terms.
`SHA256SUMS.txt` binds the delivered files. This is a research submission;
it does not silently promote the new theorem to the status of the existing
Lean/Rocq endpoint or replace any earlier ProveIt source.
