# Complete complemented three-anchor47 equation

The complete [one-page equation](equation.pdf), [standalone TeX](equation.tex)
and [literal evaluator](polynomial.json) use fifteen strictly positive
integer unknowns, 66 binary arithmetic operations with integer leaves,
and exact total degree 157. Every fixed integer is specified on the page,
including the full 436-character seed, decoder and 943 indexed tiles.

The ordinary proof, composed with the retained explicit K215/refutation
calibration, gives

\[
\mathrm{ZFC}\vdash
\bigl(\neg\exists\mathbf x\in\mathbb Z_{>0}^{15}\;P(\mathbf x)=0\bigr)
\longleftrightarrow\operatorname{Con}(\mathrm{ZFC}).
\]

This is a concrete finite specification and an ordinary proof chain
formalizable in ZFC. It is not a proof of consistency, a proof that the
equation lacks solutions, or a new end-to-end proof-assistant derivation.

## What becomes smaller

| Metric | Preserved radix55 | Complemented47 |
| --- | ---: | ---: |
| Positive unknowns | 15 | 15 |
| Integer-leaf binary operations | 66 | 66 |
| Exact degree | 157 | 157 |
| Four raw integer byte lengths, total | 242484 | **207214** |
| Complete TeX bytes | 5195 | **5145** |
| Nonwhite PDF text characters (`pdftotext -layout`) | 2764 | **2734** |
| PDF bytes | 160082 | **159762** |

Both pages use Letter paper, 9-point body mathematics and 7.7-point seed/footer
text. Raw integer storage falls 35270 bytes (about 14.5%). The printed savings
are smaller: 50 TeX bytes and 30 nonwhite extracted characters. Compression,
printed text, operation count and polynomial degree are distinct measures.
No global minimum is claimed.

The four ports change coherently. This is a different specialized polynomial
from the radix55 parent, with the same free-port evaluator. The old page is
preserved at [`../one-page-compact66-radix55/`](../one-page-compact66-radix55/).

## Mathematical chain

1. The complete
   [complemented three-anchor proof](../../research/compact66-complemented-three-anchor-radix47/README.md)
   complements every genuine color. Positive labels distinguish occupation
   from the empty zero-label cell, permitting deletion of four occupancy
   markers. Its 29-to-11 cyclic-carry argument, all 47 phases, reset fields,
   17 copies and 872 padding bits replace the earlier native decoding proof.
2. The [finite Pc3 certificate](../../research/complemented47-controller-independent/README.md)
   supplies `lambda=1012691` and new bracket residues `39,6181,1009404`
   modulo `47,8807,lambda`. Its valuation-one lift discharges the previously
   open numerical premises of that complete proof. The prime is used in
   the proof and is absent from the polynomial's constant recipe.
3. Both native/P66 witness directions are retained explicitly in section 12
   of the new proof. The actual rank is tuned, the auxiliary quotient is
   reconstructed integrally, and the actual sixth factor is `Ns=Delta`;
   the other five factors are 1. The complete K215 syntactic-refutation
   calibration remains an inherited ordinary theorem.
4. The unchanged 66-row evaluator has all fifteen variables and four ports
   live. Its factor degrees are 22,18,62,7,2,46, and the outer subtraction
   leaves exact degree157. The uniform nonzero leading coefficient includes
   `8*beta^92`; the new positive beta does not invalidate this degree proof.

The [root mathematical audit](../../reviews/complemented47-continuation-root.md)
and [independent mathematical audit](../../reviews/compact66-complemented-three-anchor47-continuation-peer.md)
record their precise reading scopes. The later
[finite/page review](../../reviews/complemented47-independent-finite-page-peer.md)
checks the discharged arithmetic, complete changed formulas and actual page.

## Reproduction and recorded checks

The newly authored [`build.py`](build.py) uses Python's standard library and
the separately reviewed small certificate verifier. It first checks that
verifier's exact source hash, then runs its read-only certificate check.
The complete old TeX and 66-gate graph are pinned by SHA-256. The exact finite
formula replacements determine the entire new TeX, so the unchanged front,
table, decoder, alphabet, seed and font declarations are checked byte for byte.

The materializer reconstructs all four integers. In particular, it evaluates
the printed indicator formula for MC and the signed telescope for MF; their
whole bytes must equal the certificate's independently constructed masks.
The four deterministic gzip files in `coefficients/` contain minimal unsigned
big-endian integers. The evaluator binds every port to its exact bytes.

```sh
python3 -B Computability/DiophantineConsistency/research/complemented47-controller-independent/certify.py
python3 -B -O Computability/DiophantineConsistency/research/complemented47-controller-independent/certify.py
python3 -B Computability/DiophantineConsistency/candidates/one-page-complemented47-independent/build.py
python3 -B -O Computability/DiophantineConsistency/candidates/one-page-complemented47-independent/build.py
```

All four default checks are read-only and passed for both author/root runs;
the independent reviewer separately checked the finite verifier and page.
To regenerate the source/ports intentionally, run the last script with
`--build`. Its checks use explicit exceptions and survive optimization.

The retained PDF was compiled by `pdflatex -interaction=nonstopmode
-halt-on-error`, with exit 0, one Letter page and no overfull boxes.
[`build.log`](build.log) preserves the actual log, including the inherited
small-font substitutions. [`equation.txt`](equation.txt) is the entire
`pdftotext -layout` stream; [`equation.png`](equation.png) is the full rendered
page inspected independently by root and peer. Both visual inspections passed.
PDF bytes and gzip wrappers can depend on tool versions; the raw integer
hashes, complete TeX and mathematical formulas identify the equation.

The frozen earlier conditional source, old certificate drafts and all
predecessor pages remain untouched. The new certificate records its own
development correction instead of changing historical evidence.
