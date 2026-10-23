# Offline coefficient and proof dependencies for Q42

This directory supplies the actual fixed coefficients, their finite construction
and independent decoder, and the ordinary mathematical proof chain used by
`../PROOF.md`. The active instance is the **entire** package 34 tuple
`mixed-parity-unrounded-1064921`. Historical coefficient manifests in the
archived Q54/Q51 source files describe older instances; they are source
provenance and are not alternate ports for Q42.

## Exact active polynomial instance

Q42's four coefficient ports are bound as follows. Each payload is a minimal
unsigned little-endian integer with no header; the `.bin.gz` file is the
authenticated compressed representation of the adjacent `.bin` file.

| Q42 port | Payload under `source34/coefficients/payloads/` | Bit length | Bytes |
|---|---|---:|---:|
| `beta` | `beta.bin` | 1,064,921 | 133,116 |
| `K0` | `K.bin` | 1,065,043 | 133,131 |
| `MC` | `MC.bin` | 1,064,921 | 133,116 |
| `MF` | `MF_source.bin` | 1,064,922 | 133,116 |

Here `beta = 2^1064921-1` and `MF_source = MF_native+2^1064921-1`.
The fourth port is already shifted. The four payloads occupy 532,479 raw
bytes and 10,466 compressed bytes. Their exact SHA256 digests and all finite
construction parameters are in
`source34/coefficients/payloads/COEFFICIENT_BINDING.json`.
`source34/COEFFICIENT_BINDING.json` gives the active compiler interface.

`source34/coefficients/build_coefficients.py` constructs all four numerals
from the included literal `k215.tm` and `wang943_tiles.json`. Its independent
partner `verify_independent.py` reconstructs and checks all 430 machine
actions, all 943 ordered tiles, 69,230 native convolution basis conditions,
all 8,801 coefficient digits, population counts, carry bounds, exact
multiplicative orders and the controller's unit conditions. It does not
import the builder.

## One offline replay command

From the Q42 directory run:

```sh
python3 verify_dependencies.py
python3 independent_algebra.py
```

Only the Python standard library is needed. The first command authenticates
all vendored source files, decompresses and checks every active numeral,
regenerates all four raw payloads into a temporary directory and compares
their exact bytes, runs the separate actual-coefficient decoder, checks the
recorded Q54→Q51→Q50→Q45 parent hashes and the explicit polynomial identities,
and writes `../DEPENDENCY_AUDIT.json`. The second independently verifies the
Q45→Q42 algebra and quartic expansion. These are finite verification steps;
the universal equivalence is established by the supplied mathematical proofs.
The historical `build_quartic50.py` uses SymPy and is preserved for provenance;
the new offline replay does not need or run it.

## Reading map for the ordinary proof

| Obligation | Local source |
|---|---|
| New simultaneous recovery of the signs of `eta,zeta`, with `w=4u²` | `../PROOF.md` |
| Q45 dyadic guard and three-coordinate positivity | `../upstream/QUARTIC45_PROOF.md` |
| Q50 removal of the packing register `G` | `source34/low_degree/QUARTIC50_PROOF.md` |
| Q51 odd-scale substitution in the quadratic lift | `source34/low_degree/upstream/ODD_SCALE_LIFTS_PROOF.md` |
| Q54 unrestricted-integer lift and exposed quotients | `20-root12/domains/DOMAIN_REDUCTION_PROOF.md` and its included source proofs |
| Exclusion of negative odd scale; canonical scale oddness | `23-separating12/proofs/ODD_SCALE_27_PROOF.md` |
| Signed-root, odd-auxiliary-multiplier and square-scale interface | `14-integer29/proofs/signed_domain_proof.md` |
| Ordinary strong rank and signed index recovery, including full local derivations | `12-gap-norm14/proofs/ORDINARY_BLANK_PROOF.md` |
| Relaxed rank, signed step-down, odd Chebyshev quotient and exposed-quotient projection | `Pell/` |
| Power recovery and half-binomial valuation/converse | `Pell/complete75_asymmetric_scale_tradeoffs.md`, `Pell/pell_kernel_half_binomial42.md`, `Pell/complete75_half_binomial_compiler.md` |
| Native carry-free window compiler | `native/FIXED_RAW_UNIVERSAL_76_PROOF.md` |
| Blank helical language and endpoint extraction | `14-integer29/dependencies/blank_helical_proof.md`, `14-integer29/dependencies/fixed_blank_67_proof.md` |
| Actual 943-tile language, compact layout and tuple transfer | `source34/coefficients/sources/WANG943_LANGUAGE_AND_COMPILER.md`, `WANG943_COMPACT_LAYOUT.md`, and `source34/coefficients/COEFFICIENT_PROOF.md` |
| Arbitrary-large cofinal padding and actual-rank tuning | `source34/coefficients/sources/PRIME_PADDING.md`, `source34/audit/COFINAL_RADIX_REVIEW.md`, and the active coefficient proof |
| Literal machine's ordinary ZFC calibration and formal endpoint statement | `K215/proof.md`, `K215/KEndpoint215.lean` |

The copy `29-simpler-forms/integer54_quartic.json` is the exact archived parent
whose digest is recorded in Q51. The separately included original package-20
Q54 file is historical source data. The replay checks the exact archived
parent rather than disregarding a metadata or whitespace hash discrepancy.

### Transport-coordinate correction

The authenticated Q45 prose has an off-by-one spelling in its final transport
step: it writes the old product coordinate `z-1`. The actual Q45 and Q50
residuals, and Q42, have

```text
(K0+w) C - F - z(q-1) = 0.
```

Thus the restored guard is `z>0`. The old product coordinate is `z_old=z+1`.
Once `X=2^R` and `R>3q` are recovered, `w=X/q>q`, while `C>=1` and `F<q`.
Consequently `(K0+w)C>F`; with `q-1>0` the displayed identity forces `z>0`.
That is exactly the guard needed by Q50. The erroneous stronger conclusion
about the differently named coordinate is not used. The new Q42 rank and
sign argument does not use `z`. The new replay checks the literal transport
row explicitly; the upstream proof is preserved unchanged as evidence.

## Pins, attribution and proof scope

Every source in `SOURCE_PINS.json` has its exact repository path, commit,
Git blob SHA1, byte length and SHA256. The current collection pin is
`beb0192cb8dc36f78c369c080f2adfbc1887a486`; historical files are fetched at the
exact earlier pins recorded in their manifests. Sources were read as inert
text or data. Included original licenses and notices are under
`source34/LICENSE`, `source34/licenses/`, `23-separating12/licenses/`, and
`20-root12/LICENSE.ProveIt`. No upstream mathematical prose is silently
edited. `../upstream/INHERITED_ORDINARY_PROOF.md` is an exact duplicate of the
authenticated source-12 proof.

The archive is sufficient to reconstruct and check the fixed polynomial and
to read the ordinary Pell, coefficient and reduction arguments offline.
The K215 theorem is an inherited calibrated endpoint. Its included Lean file
states the exact unconditional biconditional with `BProv ZFCax_s [] Form.fBot`;
the full transitive Lean/Rocq project and runtime-verification artifacts are
not copied here, and this package does not claim a fresh formal build or an
internally encoded ZFC proof certificate. The machine-calibration exposition
retains explicit links to those inherited developments. This is the same
ordinary-mathematical dependency boundary as the source collection.
