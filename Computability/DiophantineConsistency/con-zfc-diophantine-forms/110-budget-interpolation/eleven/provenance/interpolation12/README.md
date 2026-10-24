# Twelve integer variables through interpolated Pell certificates

Research contribution prepared for Vladimir Reshetnikov's ProveIt project,
24 October 2026.

**Main result:** an explicitly specified ordinary integer polynomial in
**12 unrestricted integer variables**, of **exact total degree 4,832**,
computed by **248 live binary arithmetic operations**, whose lack of
integer zeros is provably equivalent in ZFC to syntactic `Con(ZFC)`.

The new arithmetic proof composes with the completed ordinary native/compiler
and K215 calibration proofs retained in this archive. This contribution
does not supply a new end-to-end proof-assistant certificate or an encoded
derivation in the repository's internal ZFC calculus.

## Read first

The complete manuscript is `report/report.pdf`; its editable sources are
`report/report.tex`, `report/trace13.tex`, and
`report/coefficient_recipe.tex`.

The archive is self-contained for its finite arithmetic checks. It includes
the actual six fixed numeral payloads, their finite reconstruction recipe,
943 ordered tile records, the 430-action machine table, the inherited ordinary
proofs, and applicable licenses. No coefficient is an unspecified index,
a value selected by a proof search, or a consistency-dependent choice.

## Delivered equations and exact metrics

| Literal equation | Domain | Variables | Exact degree | Operations | Add / multiply / subtract |
|---|---|---:|---:|---:|---|
| `equations/monotone_intersective12_degree4832.json` | Z | 12 | 4,832 | 248 | 64 / 153 / 31 |
| `equations/monotone_intersective12_degree16000.json` | Z | 12 | 16,000 | 223 | 53 / 139 / 31 |
| `equations/trace13_degree1072.json` | Z | 13 | 1,072 | 190 | 40 / 118 / 32 |
| Inspected incoming baseline, unchanged under `inherited/root_fusion/` | Z | 13 | 1,088 | 195 | See original metrics |

The twelve-variable coordinates are exactly

~~~text
j, C, z, h, r, v, w, T, c, n, t, s.
~~~

Capital `C` and lowercase `c` are distinct. All intermediate registers are
polynomial abbreviations, not additional existential coordinates. Every
exported node, coordinate, and fixed coefficient leaf is live.

An operation means a binary addition, subtraction, or multiplication.
Squaring is charged as a multiplication, multiplication by a fixed scalar
is charged, and reuse of an already computed register is free. The totals
include the complete five-radical norm and all denominator clearing.

The degree-16,000 companion uses fewer operations. The degree-1,072
companion improves the inspected thirteen-integer baseline in both degree
and operation count. These are explicit tradeoffs, not claims of global
minimality or a world variable-count record. The inspected repository
already has ten-integer equations of substantially larger degree.

## The two principal ideas

### 1. Interpolate first, then share the witness

The main construction uses

~~~text
Pi(x) = (x^2 + 31)(x^3 + x + 1).
~~~

This polynomial has a root modulo every positive integer, no root in a real
field of degree at most two over Q, and positive derivative everywhere.
Homogenizing it and reducing modulo the main Pell relation `d^2 = Dm`
gives `A + B*d`, with a strictly positive polynomial coefficient `B`.

The carrier simultaneously restores the main Pell congruence and excludes
the entire zero-multiplier branch. A positivity witness can consequently
be shared with the normalized strong Pell witness through `I = s*r*c^2`.
The auxiliary Pell coordinate `T` can serve as the intersective residue:
the interpolation theorem first fixes a suitable `I,f`, then realizes
every residue class of `T mod I` while preserving the auxiliary equation.

This order of quantifiers matters. Ordinary existence of infinitely many
Pell solutions would not suffice. The proof uses the period `4*m*f`
modulo `f^2` and a Lucas valuation bound to establish CRT compatibility.
The normalized strong equation directly supplies its rank conclusion;
no odd-multiplier assumption is made.

The final degree reduction uses the carrier's homogeneity:

~~~text
B*sqrt(Dm)/abs(S) < 256*(T^2+c^2+1)^2.
~~~

Successive odd product weights separate the other roots. They are nonzero
before the guards are proved; the single imaginary radical argument then
recovers positivity before any positive bounds are invoked.

### 2. Take the rational trace before separating radicals

The thirteen-variable companion extracts a congruence from a vanishing
radical norm using normalized field trace. Irrational square roots have
rational trace zero, even when different irrational terms cancel.

This restores the full large odd scale before individual square roots have
been proved integral. It makes the earlier guard multiplier and enlarged
main-radical weight unnecessary. Reusing the established first-Pell
factorization saves one additional operation. The result is degree 1,072
and 190 operations.

## Exact polynomial specification

For five formal radicands, write

~~~text
F32(Z;A0,A1,A2,A3,A4)
  = product over eps in {+1,-1}^5 of
      (Z - sum_i eps[i]*sqrt(Ai)).
~~~

Sign invariance makes this a fixed ordinary polynomial with integer
coefficients. The delivered graphs contain no square-root operation,
division, variable exponent, oracle, or hidden quantified parameter.

For the twelve-variable principal equation, the radicand degrees are

~~~text
70, 190, 212, 250, 302.
~~~

The final radicand is uniquely highest. Its sixteenth power is the entire
degree-4,832 homogeneous contribution. In particular,

~~~text
[j^2560 w^544 v^672 h^64 s^192 r^224 c^384 T^192] P
  = 2^5024 * 3^3120 * beta^2560 > 0.
~~~

The builder gives the equally valid other binomial endpoint,
with `s^256 r^160` instead of `s^192 r^224`. Both coefficients agree.
The exact degree is established after specializing the actual fixed
coefficient tuple, not merely for generic symbolic coefficient ports.

See `equations/SCHEMA.md` for the literal graph format and
`equations/METRICS.json` for the machine-readable census.

## Reproduce the finite checks

Python 3.10 or later and its standard library are sufficient.
Run from the archive root:

~~~bash
python3 verify.py --receipt /tmp/conzfc-verification.json
python3 -O verify.py --receipt /tmp/conzfc-verification-optimized.json
~~~

The verifier authenticates inherited primitives, reconstructs all six
coefficient numerals, regenerates the three graphs and compares their exact
JSON bytes, and checks their topology, arithmetic census, formulas, and
degree evidence. It also checks all files listed by `MANIFEST.json`
when that manifest is present. It does not modify the delivered equations.
Use a receipt path outside the archive to leave the release manifest intact.

The independent twelve-variable checker imports no producer module. It
checks the quintic remainder and positive coefficient identities, numerical
bounds, modular interpolation fixtures, a separately implemented formal
32-conjugate product, exceptional zero slices, and an intentional coefficient
corruption. The thirteen-variable checks use exact sparse polynomial
identities and a separately written front end.

The finite checks establish the specified finite claims only. They do not
prove the unbounded compiler, Pell interpolation, or consistency theorems,
and do not use a bounded failure to find zeros as evidence for consistency.
Those unbounded arguments are supplied as ordinary mathematical proofs.
The independent reviews were conducted during this research session;
they are not external human peer review.

To regenerate individual graphs:

~~~bash
python3 build_twelve.py --variant product \
  --output /tmp/monotone_intersective12_degree4832.json

python3 build_twelve.py --variant compact \
  --output /tmp/monotone_intersective12_degree16000.json

python3 build_trace13.py --base inherited/root_fusion --out /tmp/trace13
~~~

The JSON coefficient and proof paths are relative to their delivered
`equations/` location. An equation regenerated into `/tmp` retains these
intended package-relative links.

To compile the manuscript, with a standard TeX Live installation:

~~~bash
cd report
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
~~~

## Source snapshot, attribution, and integration

The inspected commit is

~~~text
04a1d79222d55cabe4ba52897863fc33baa8c268
~~~

Repository:
https://github.com/VladimirReshetnikov/ProveIt/tree/04a1d79222d55cabe4ba52897863fc33baa8c268

`provenance/REVIEWED_INCOMING.json` records hashes and pinned URLs for all
15 inspected incoming ZIP archives. The whole original
`ConZFC_13_Integer_Norms_2026-10-24.zip` package is retained unchanged under
`inherited/root_fusion/`, apart from omitting runtime-generated cache files
that were not part of its archive. Two additional signed guard proofs and
their notices are preserved in `provenance/signed_guards/`.
`provenance/INHERITED_FILES.json` records the original byte inventory.

The six-port tuple is a single coherent object. `MF` is already shifted:
`MF = MF_native + beta`. Shifting it twice, replacing only one port, or
mixing coefficient families changes the polynomial and breaks the theorem.

The new work is the combined interpolation/carrier reduction, its
homogeneous product-weight implementation, and the trace-before-separation
companion. The general intersective technique, Pell positivity criterion,
native encoding, determinant guard, adjacent-coefficient descent, and first
norm factorization are explicitly credited in the manuscript. The particular
combination is proposed as a new research contribution; no exhaustive claim
of historical priority is made.

For incorporation, preserve this package as a new research contribution,
retain the source snapshot and coefficient bindings, and link its manuscript
and metrics from the appropriate collection index. No remote repository
was changed or published during preparation of this archive.

## Archive map

- `report/`: complete TeX sources and compiled PDF.
- `equations/`: three literal polynomial graphs, schema, and metrics.
- `proofs/`: complete new proofs and independent mathematical reviews.
- `build_twelve.py`, `build_trace13.py`: reproducible graph builders.
- `check_twelve.py`, `verify.py`: finite verification entry points.
- `verification/`: normal and optimized verification receipts and PDF QA.
- `provenance/`: source ledger and additional unchanged signed proofs.
- `inherited/root_fusion/`: unchanged source package, including its coefficient
  payloads, bounded recipe, ordinary calibration proofs, and licenses.
- `MANIFEST.json`: SHA-256 inventory of the delivered files.
- `LICENSE`, `NOTICE.md`: licensing and attribution information.
