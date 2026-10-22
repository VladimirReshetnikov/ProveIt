# Smaller unrestricted-integer equations

All circuits are explicit arithmetic skeletons with four fixed coefficient ports. Use `COEFFICIENT_BINDINGS.json` for the primary complete Wang943 coefficient tuple; `COEFFICIENT_TRANSFER.md` explains why the signed-domain proof transfers and distinguishes the retained original06 alternative. Never mix individual ports across backends. MF is always shifted.

| Circuit | Integer variables | Exact degree | Operations | Multiplications / additions |
|---|---:|---:|---:|---:|
| `integer26_unscaled_four_root192_degree2465.json` |26|2465|192|117 /75|
| `integer27_weighted_root136_degree1116.json` |27|1116|136|72 /64|
| `integer28_normalized_amalgam128_degree258.json` |28|258|128|66 /62|
| `integer28_gap_norm127_degree426.json` |28|426|127|66 /61|

The dominated earlier scaled-auxiliary construction `integer26_four_root194_degree3185.json` (26 variables, degree3185,194 operations) remains as provenance. The new unscaled construction applies rational auxiliary Pell saturation before recovering gamma and saves two gates while lowering the degree by720.

Every arithmetic operation is binary addition, subtraction or multiplication, including operations with fixed numerals. All gates and ports are live. The consistency equivalences are ordinary mathematical proofs formalizable in ZFC, not newly Lean/Rocq-certified results. There is no global minimality or consistency claim.

The count reduction uses the same seven positive original ports J,F,alpha,z,s,eta,zeta, each represented by three unrestricted integers. The normalized strong multiplier is odd and the power scale is a square. The remaining coordinates may be signed; the proof notes explicitly exclude all dangerous zero-denominator branches. The26-variable equation additionally uses the rational auxiliary Pell saturation lemma and Galois separation.

## Proofs

- `INTEGER26_UNSCALED_PROOF.md`: main four-root norm, saturation-first signed and zero branches, exact degree2465.
- `INTEGER26_PROOF.md`: retained scaled-root predecessor, exact degree3185.
- `INTEGER27_PROOF.md`: three-root norm, signed h/t/T bounds, exact degree1116.
- `INTEGER28_AMALGAM_PROOF.md`: two-root merger with normalized strong guard, exact degree258.
- `INTEGER28_PROOF.md`: gap root elimination, exact degree426.
- `../audit/FINAL_WEIGHTS_AND_INTEGER26_AUDIT.md`: independent root/sign audit.
- `../audit/UNSCALED_SATURATION12_26_AUDIT.md`: independent audit of the dominating unscaled construction.
- `../audit/INTEGER27_INDEPENDENT_AUDIT.md`: independent signed weighted-root audit.
- `../audit/RATIONAL_AUXILIARY_PELL_SATURATION.md`: independent saturation lemma.

## Reproduce finite checks

Run from this directory with Python3 and its standard library:

    python3 replay_integer_forms.py

This verifies every local upstream source hash, rebuilds and checks all five circuits (including the retained predecessor), verifies all arithmetic binding hashes, and verifies the exact materialized primary coefficient bytes and bit lengths. It writes `FULL_INTEGER_REPLAY.json`. The compact coefficient `.bin` files must first be inflated if the portable package distributes them compressed. An optional `--all-backends` flag additionally requires and verifies the separate d=5^11 fallback binaries; those need not accompany the portable primary package. The individual commands are:

    python3 build_integer26_unscaled.py
    python3 verify_integer26_unscaled.py
    python3 build_integer26.py
    python3 verify_integer26.py
    python3 build_integer27.py
    python3 verify_integer27.py
    python3 build_integer28_amalgam.py
    python3 verify_integer28_amalgam.py
    python3 build_integer28.py
    python3 verify_integer28.py

The main26 emitter uses the exact frozen sibling `../roots/root12_saturated_product.json`; the predecessor uses `../roots/root12_scaled_y_product.json`. The other emitters read pinned upstream JSON saved beneath `upstream/`. All upstream inputs are treated only as inert data. No upstream Python program is executed and no installation is needed.

The `INTEGER*_CHECKS.json` receipts record independent formula or formal-algebra evaluations, live-gate checks and exact modular leading-coefficient tests. These finite diagnostics supplement the mathematical proof rather than replacing its unbounded Pell/compiler dependencies. They do not claim a K215 accepting computation or evaluate the final polynomial on an enormous actual witness.

`SOURCE_MANIFEST.json` records the pinned repository sources, Git blob identities and local SHA-256 hashes. The coefficient backend includes separately materialized exact integers; its generation and semantic audit live in the sibling compiler directory.
