# Independent finite-controller and rendered-page review

Date: 2026-10-25. Reviewer: `/root/complemented47_review`.

**PASS, with the scope below.** The new independently authored finite
verifier discharges Pc3 for the exact complemented three-anchor radix47
recipe. The candidate page matches that recipe and the retained whole
P66 front. The final rendered page passed a second visual inspection.
No verifier, candidate source, frozen proof, or earlier review was edited
by this reviewer; no commit was made.

This review supplements the unchanged
[`compact66-complemented-three-anchor47-continuation-peer.md`](compact66-complemented-three-anchor47-continuation-peer.md).
That earlier review correctly recorded the finite conditions as open at
the time. The new evidence closes those conditions; it does not convert
the ordinary inherited calibration into a kernel-checked formalization.

## Exact verifier and evidence

I read the complete final 297-line
[`certify.py`](../research/complemented47-controller-independent/certify.py),
its complete README, and the certificate. The source has 14683 bytes and
SHA256 `318665c36d7600a99dbddbacca11ef9a2d30f65e04a761efe25d1f3653e662ed`.
The saved certificate has SHA256
`f95746541354778fd4f5942a58c0f11c238388017f55b249ff7ca4760c73ee7b`.
Its inputs bind the retained radix55 TeX
`440cf0853ec2f992db7aa6146aec42c189368375d8db725d3df085ca27dc4dff`
and the complete frozen complemented47 proof
`ab3211b4d9aa7842531a77fde938092c7d96e5cb8dcfdf94bf2b695e156d1ae2`.
The verifier's final README hash was
`c70e735890be7cb2792954ca9fb7911d32b2519a1da9b4760b5616df67154e4c`.

I independently executed both read-only commands from the repository root:

```sh
python3 Computability/DiophantineConsistency/research/complemented47-controller-independent/certify.py
python3 -O Computability/DiophantineConsistency/research/complemented47-controller-independent/certify.py
```

Both exited 0, reproduced the exact saved certificate bytes, and reported
the same passing Pc3, prime, residues and constant-byte total. All actual
checks use `require` and remain active under `-O`. The default mode writes
no certificate; only the explicitly selected `--write` mode can do so.
No incoming archive code, project module, or earlier numerical certificate
is executed or imported by this verifier. Its shared mathematical input
is the full reconstructed tile table, not an independently reconstructed
table for each modular route.

## Finite mathematics checked

The seed extraction retains all 436 characters. Prefix counters in the
430-action decoder implement the printed empty-prefix convention; the
first action is checked. Every indexed tile family is transcribed,
including initializer `(3,436,4,4)`. Exact index coverage and distinctness
give all 943 tiles, while the color checks establish the full positive
complemented label ranges.

All 3297 coefficients are reconstructed, including the four absent
occupancy markers and both zero-coefficient dummies. The selector formula
and all four copied-label groups equal section 4 of the frozen proof.
The three anchors have coefficient `2^44`.

The two modular routes are algebraically distinct. Dense Horner evaluation
at `rho^-1` implements the reciprocal formula, while the second route
expands every selector and control into positive powers without using the
coefficient array or reciprocal. Each route includes the spatial term
`rho^8849`. Full-integer B, K and H reductions supply a third comparison
against those routes. The results are:

| Modulus | B | K | H = 1 + BK + B² |
| ---: | ---: | ---: | ---: |
| 47 | 12 | 46 | 39 |
| 8807 | 2677 | 7695 | 6181 |
| 1012691 | 959313 | 26931 | 1009404 |

Trial division checks all possible prime divisors through the integer
square root. It proves `lambda=1012691` prime, with bound 1006. Also
`lambda>d=413929` and `lambda-1=10*101269`. The exact order tests use all
prime divisors of `4403=7*17*37`; the earlier development assumption that
4403 was prime is absent from the final verifier and disclosed in its
README. The order/gcd checks establish the required orders 23 and 4403
for B at the two fixed primes.

At lambda, `B²=511101`, which is not 1, and
`B^(lambda-1)=285921151559=1+lambda*282338 mod lambda²`.
Because `0<282338<lambda`, the valuation is exactly 1. All three H
residues are nonzero. These facts establish every new section 11 finite
premise for this precise K; no controller from a different tuple is reused.

The exact-integer construction also agrees with both masks in the frozen
proof. In particular, the positive padding sum equals its telescoped
spelling, and `MF_source=MF_native+beta` is checked exactly once. It yields
982 physical positions, 980 nonzero coefficients, padding population 872,
native population 982, and MC population `412947=d-982`, with all stated
scalar boxes and origin residues. The four minimal unsigned big-endian
integer encodings total 207214 bytes. This is a raw-numeral metric; it
does not measure polynomial degree, rendering, or global simplicity.

## Complete materializer and evaluator binding

I additionally read the entire 150-line
[`build.py`](../candidates/one-page-complemented47-independent/build.py),
SHA256 `f9b0b01474f202e380ceafcf517d0e3baacac34d5bc103495d3f58c668ef8567`.
It authenticates the reviewed verifier before invoking or importing it,
and authenticates the entire parent page and parent polynomial. Its exact
text substitutions, including the complete replacement Phi block, determine
the whole new TeX. There is no unreviewed incoming generator in this path.

The materializer uses the printed nonzero-coefficient indicator for MC,
including both explicit dummy corrections, and the signed MF expression.
The coefficient maximum is below rho, so the printed floor indicator is
indeed exactly the positive-coefficient test used in this implementation.
The four reconstructed whole integers must agree with the certificate's
raw-byte hashes and lengths before their gzip wrappers are accepted.

The complete parent arithmetic graph is copied, with its coefficient binding
replaced as a whole. I read all 66 rows of the pinned parent graph: its
port names `K0` and `MF` map respectively to the new K and once-shifted
MF_source. The inherited formula has the stated multiplication/addition/
subtraction counts, and the reachability check covers every gate, variable
and fixed port. This is a full unchanged graph transfer at the new exact
ports, not a sampled numerical polynomial comparison or a new independent
symbolic degree derivation.

After ROOT materialized the artifacts, I independently ran both commands:

```sh
python3 -B Computability/DiophantineConsistency/candidates/one-page-complemented47-independent/build.py
python3 -B -O Computability/DiophantineConsistency/candidates/one-page-complemented47-independent/build.py
```

Both exited 0 and reproduced all six generated files exactly: the TeX,
polynomial and four compressed integer ports. The final polynomial SHA256
is `93322aaec1a113a2f42b47b083577173cb14e41dcd3f6691c3c07a444b3e220c`.
The `-B` option prevented import cache writes; neither command used `--build`.
All guards remain active under optimization. Compression-wrapper bytes
can vary across Python versions; the raw-integer hashes define the ports.

## Whole candidate source comparison

I read the entire final
[`equation.tex`](../candidates/one-page-complemented47-independent/equation.tex)
and its complete diff against the retained radix55 page. Its 5145 bytes
have SHA256
`f28911a9c96e53cd5c3b2e94bdd72322fc065e05d0ace617edff26a5d2322ebd`.
An additional exact text comparison confirmed that the whole arithmetic
front, all fifteen positive domains, and the whole table/decoder/alphabet/
seed portion are byte-for-byte unchanged. The fonts remain 9-point body
and 7.7-point seed, with the same page and column settings.

Every changed mathematical formula matches the frozen new proof:

- `rho=2^47`, with the same cell length and reciprocal centers.
- `mu=2^46-2`, copy lengths 9 and 8, and padding
  `-rho^8792+2^26*rho^7694-rho^7691` in the once-shifted source mask.
- Selector coefficient `1+2^10*(1+w+2^8*n+2^17*p+2^25*s)`.
- The two unchanged full label-control groups and exactly three equal
  `2^44` anchors, with the four old occupancy controls removed.

The unchanged indicator expression for MC now consumes the new Phi, so
it omits those four positions and still corrects the forbidden selector
and both dummy positions as proved. The original tile table is intentionally
retained: the positive selector formula already incorporates the complete
color complementation. No separate complemented table is needed to define
the four constants.

After finite discharge, the footer states the ordinary equivalence without
an unresolved Pc3 condition. It retains the explicit limitation about
Lean/native calibration and correctly says the page is a specification,
not an unsolvability proof.

## Second rendered-page inspection

I viewed the complete final PNG generated by ROOT from that final TeX.
The arithmetic front, boxed equation, all four constants, complete Phi,
entire indexed table, decoder, alphabet, all eight seed lines and footer
are visible. Superscripts, signs and delimiters remain legible. I found
no clipping, column collision, omitted line or misleading formula break.
`pdfinfo` reports one Letter page, 612 by 792 points, 159762 bytes.
The full log has no Overfull, Underfull or TeX error diagnostic.

The rendered files were first inspected under
`/tmp/diophantine-complemented47-page/`. I then independently confirmed
byte-identical copies at the stable candidate paths below:

| File | SHA256 |
| --- | --- |
| [equation.pdf](../candidates/one-page-complemented47-independent/equation.pdf) | `180da9b637f8cc220392047d6a8be2cc92c3212c5482073a3f444c68f39c62f5` |
| [equation.png](../candidates/one-page-complemented47-independent/equation.png) | `2f9998347ffdb802449a87c71c8fb3e9a2abc7e5f26310fa453cd7cc35cba742` |
| [equation.txt](../candidates/one-page-complemented47-independent/equation.txt) | `5a4e006c39f53b8f79d04ed5cddbe5c4a6852514c16eb215afa6d370c055e605` |
| [build.log](../candidates/one-page-complemented47-independent/build.log) | `8ef165ad38dac9f65b90a338ee2a7fe186e0dafec2f14e28c408691c0ea5c9d7` |

I independently extracted the retained radix55 PDF with `pdftotext -layout`.
Removing all whitespace from that output gives 2764 characters, versus
2734 for the new page's `-layout` output: a reduction of 30 under this exact
extraction convention. Plain `pdftotext` gives a different old count, so
the metric must retain the `-layout` qualifier. This is a reproducible text
metric and visual review, not a claim to count mathematical glyphs exactly.

## Scope of the consequence

Together with the separately reviewed whole ordinary proof, the finite
certificate removes its outstanding Pc3 condition and supports the stated
positive-solution/refutation equivalence for this exact tuple, relative to
the retained arithmetic, language and foundational calibration contracts.
The page supplies the full finite coefficient specification. These checks
do not independently formalize the transitive K215 calibration or the
ZFC proof, decide consistency, establish a global minimum, or authorize a
different future tuple by analogy.
