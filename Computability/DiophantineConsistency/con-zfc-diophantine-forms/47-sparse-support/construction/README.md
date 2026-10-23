# Supported-monomial coding for explicit consistency equations

Pinned repository: ProveIt at `124c07c0b77a9e20e84676514d8b1ff78536ea3f`.
The main mathematical proof is `SPARSE_PROOF.md`; the enclosing research
article explains the endpoint dependencies and comparisons.

Three source transformations improve the existing low-variable equations:
only monomials actually used by the source must be isolated, the
nine-variable digit base can be a fixed multiple of a square, and a redundant
common shift of the target exponents can be removed. All final
expressions are literal addition/subtraction/multiplication circuits with
fixed integer coefficients. Intermediate register names are abbreviations,
not additional quantified unknowns.

| W | Positive unknowns | Degree | Operations |
|---:|---:|---:|---:|
| 239 | 9 | 25,936,016 | 651 |
| 220 | 9 | 23,878,392 | 670 |

The corresponding nine-nonnegative-variable circuits use 655 and 674
operations. Separate equations over **ten unrestricted integers** have
degree/operation points 71,151,176 / 662 and 65,506,504 / 675.

The comparator at the pinned snapshot is package 45's nine-positive
788-operation, degree-129,875,980 equation and package 40's ten-integer
782-operation, degree-237,520,456 equation. The very short 67-operation
many-variable family is a different comparison and remains unbeaten here.
No global minimum or reduction below nine natural or ten integer unknowns
is claimed.

## Exact definition and fixed coefficients

- `generated/*_nine_positive.json`, `*_nine_natural.json`, and
  `*_ten_integer.json` are the main arithmetic DAGs. Each records its domain,
  named registers, live operation counts, coefficient recipes, and degree.
- `generated/*_nine_*_degree_certificate.json` are larger, exactly equal
  polynomial circuits in which the leading cancellation is resolved.
- `parent_system.json` is the exact pinned 31-variable, 22-residual parent.
- `targets_sparse220.json` and `targets_sparse239.json` specify every
  supported source term, its coefficient and its exponent position.
- `coefficients/` contains the whole original four-port tuple and every
  actual fixed leaf of the nine- and ten-variable circuits. Nothing is
  selected according to whether ZFC is consistent.
- `fixed_coefficients.json` and `fixed_coefficients10.json` give complete
  recipes, encoding rules, compressed/raw hashes and payload paths.

## Reproduce

Python 3.10+ and only its standard library are required:

```sh
python3 verify.py
python3 -O verify.py
```

The verifier checks hashes and recipes, source-term reconstruction, all
supported-monomial isolation conditions, all target interactions, gate
liveness and operation counts, exact polynomial identities and degrees,
and domain translations. It regenerates the delivered data in a temporary
copy and requires exact byte equality. The release remains unchanged.

New coefficient payloads use `canonical_gzip.py`, which fixes the gzip
header, timestamp, flags and OS byte explicitly; Python-version or host-OS
defaults cannot change those bytes. The reference encoder is level-9 raw
DEFLATE with zlib 1.3.2 under CPython 3.12.14. Bit-identical compressed
regeneration additionally depends on reproducing that DEFLATE stream;
decoded coefficient values have separate authoritative raw-byte hashes.

The independent nine-variable audit expands both finalizer expressions in
an abstract polynomial ring, compares their 232 terms exactly, and proves
the leading coefficient symbolically as
`2^2050 * base_scale^(54148*W+26496)`. The ten-integer degree certificates
give a nonzero leading coefficient modulo a prime at the propagated total
degree upper bound; this is an exact nonvanishing argument, not sampling.

The optional `search/` directory preserves the finite heuristic weight
search which found the literal vectors. The proof needs only the delivered
vectors and their exhaustive finite isolation certificates, so running the
search is unnecessary for verification.

## Proof boundary

The source transformations and zero-existence adapters are ordinary
mathematical proofs formalizable in ZFC. They preserve the inherited parent
quadratic system, using the explicitly identified Jones/Sun arithmetic
theorems. Connecting that parent to a syntactic ZFC refutation imports the
repository's compiler and literal-machine calibration. This package does
not close the documented compiler-to-ZFC formalization gap or export a new
object-language ZFC derivation. Finite verification does not decide the
existence of a zero and does not prove Con(ZFC).

Read `NOTICE.md` and `licenses/` before incorporation. This package introduces
no external publication or repository mutation.
