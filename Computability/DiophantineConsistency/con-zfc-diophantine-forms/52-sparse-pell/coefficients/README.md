# One coherent native coefficient tuple

These four raw integers and deterministic gzip files were independently
reconstructed from the finite formulas in package 44 and the literal Wang943
tile list. Every raw and gzip hash agrees with both package 44 and package 39's
compact instance at ProveIt commit
`124c07c0b77a9e20e84676514d8b1ff78536ea3f`.

The tuple is `wang943-complement67-shared-anchor-length8807-prime581197`,
with native base `B=2^590069`. It occupies 295,388 raw bytes or 9,445 gzip bytes.

| Arithmetic port | Payload | Bit length |
|---|---|---:|
| beta | beta.bin | 590069 |
| K0 | K.bin | 592884 |
| MC | MC.bin | 590069 |
| MF | MF_source.bin | 590070 |

Use all four ports together. `MF_source` already equals the native high mask
plus `B-1`; do not shift it again. `COEFFICIENT_BINDING.json` is the authoritative
binding, including file hashes and the parent-system identity.

## Common quadratic parent

The chosen parent is package 31's 60-operation system of 22 quadratic
equations in 31 strictly positive variables, retained byte-exact as
`../review/sources/31-sun10/quartic31/quartic31_system60.json`.
Its SHA256 is
`ac2a67782d344d1e74fd93bc3f09fae0097eaed1829fd8194ae235ae84763e48`.
Its old embedded binding metadata is historical; this directory replaces
the entire tuple through the package-44 adapter, not one coefficient at a time.
The package-31 quadratic refactor is an identity with all four ports symbolic.
The new native adapter supplies the same normalized compiler interface.
Composition gives the same positive-solvability/refutation equivalence,
with the inherited compiler and K215 calibration as mathematical dependencies.

The parent's `z` is already shifted: `z_old=z+1`. This is not a bijection of
arbitrary positive assignments. On a source zero the compiler gives
`C=q-F-alpha>0`, `F<q`, `X=wq=2^R`, and `R>3q`, hence `w>q>F`. Therefore
`(z_old-1)(q-1)=(K0+w)C-F>0`, implying `z_old>=2`. Thus the shift is reversible
on solution sets for the complete authentic new tuple too.

## Independent finite checks

Run `python ../review/check_native_independently.py` from this directory.
It reads inert pinned JSON and the textual recipe; it imports or executes
no upstream program. It reconstructs all four ports and checks:

- the 943-tile hash and distinctness;
- 66,062 complete basis identities and 38,663 one-bit decoder mutations;
- synchronization intersections, carry inequalities, padding, mask balance;
- controller primality, exact multiplicative orders, lifting and unit residues;
- every retained Git blob pin and each complete-tuple raw payload hash.

`../review/NATIVE_INDEPENDENT_CHECKS.json` records the result. These are finite
interface/data checks, not a new unbounded compiler proof or formal certificate.

Run `python ../review/check_parent_coefficients.py` to expand the parent
independently after replacing every positive variable by `n+1`. The 136 exact
symbolic coefficient records and conservative bounds are in
`PARENT_COEFFICIENT_BOUND.json`. In port order `(beta,K0,MC,MF)`:

- bit lengths are `(590069,592884,590069,590070)`;
- raw coefficient triangle bounds have maximum bit length 1,182,954;
- factorial-weighted quadratic records satisfy `|c|<M=2^1182955`;
- the old Jones-source proof permits `base_floor=4096M=2^1182967`;
- `beta_source=2^1182966` is even-exponent and strictly exceeds
  `4*33^2*max(raw coefficient triangle bounds)` for the direct Sun source.

The latter bounds are sufficient portable source bounds, not claimed optimal
constants. Downstream changes to the source must check their own precise bounds.

The inherited notices and licenses are retained under
`../review/sources/44-b4-sparse/native/licenses/` and its `NOTICE-upstream.md`.
