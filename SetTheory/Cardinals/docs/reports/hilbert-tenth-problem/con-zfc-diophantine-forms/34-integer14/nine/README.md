# Signed-quadratic nine-variable synthesis

The selected equation is `nine31_signed_quadratic.json` over nine nonnegative
integers: **1,559 binary operations, exact degree 92324·5^32+296**.
The strictly positive translation is `nine31_signed_quadratic_positive.json`:
**1,554 operations**, same degree. The diagonal leading coefficient is 2^192.
Both use 80 nonliteral fixed leaves, not 80 additional unknowns.

Read `SIGNED_QUADRATIC_NINE_PROOF.md` for every polynomial abbreviation, the
new signed quadratic bounds, the zero-margin-safe signed finalizer, and the
mathematical consistency equivalence. `QUARTIC31_PROOF.md` gives the inherited
parent elimination; `quartic31.json` is the active parent system.

## Binding

`INDEX_CONSTANTS.json` is authoritative. All four ports come together from
`../coefficients/payloads/COEFFICIENT_BINDING.json`, variant
mixed-parity-unrounded-1064921. The adapter is in
`../coefficients/COEFFICIENT_PROOF.md`; MF always means MF_source.
The source arithmetic circuit `base31.json` is generic inert JSON.
`quartic_coefficients.json` gives the 402 weighted coefficient recipes.

`INDEX_BOUND.json` proves z=2^4259933 works. Its actual bytes are in
`z_index.bin` and `z_index.bin.gz`. `FIXED_LEAF_PAYLOADS.json` specifies all
78 distinct nonliteral coefficient payloads in `fixed_leaf_payloads/`.
They are gzip-compressed minimal unsigned little-endian magnitudes, with
signs in the manifest. The only unmaterialized active leaf is y_index,
whose bounded58,905-term definition is explicit. No unspecified r.e. index.

Historical files under `upstream/` are inert source references, not current
bindings. `PORTABILITY_TRANSFORMS.json` records the metadata-only parent
rebind; all residual equations and coefficient recipes are unchanged.

## Reproduce

With Python 3.10+ and the sibling coefficients folder available:

- `python build_signed_nine.py`: regenerate the four arithmetic variants.
- `python check_degree.py`: exact cancellation-free degree certificate.
- `python check_signed_nine.py`: algebra, aliases, root bounds, finalizer.
- `python check_actual_index.py`: actual tuple, all 402 exact coefficient bounds,
  78 materialized leaf recipe identities, z and modular instance checks.
- `python bind_index.py`: regenerate finite indexbound andz.
- `python materialize_fixed_leaves.py`: regenerate the 78 compressed leaves.

Gzip headers can vary across Python/platform versions. Verify stored gzip
hashes and decompressed raw magnitudes, not regenerated gzip byte identity.
All routines are standard-library-only; no upstream program is imported.
The proof is mathematical and imports the existing compiler/Jones/K215
calibration. No new Lean/Rocq endpoint, no consistency proof and no global
optimality claim.

For a smaller exploratory baseline, `nine31_structured*.json` combines the
older package28 majorants with the new finalizer; its degree is
93264·5^32+288 and its costs are 1560 natural/1556 positive. It is dominated
by the selected signed-quadratic form and retained only for comparison.
