# Explicit signed Jones syntheses

Pinned source: VladimirReshetnikov/ProveIt at 8c6eec9d19ef80538c8e61ff6e0180040583446a.

Results, with L=5^32:

- 14 unrestricted integers: degree 813056 L+2752; 1524 binary +,−,× operations.
- 16 unrestricted integers: degree 406528 L+10008; 1537 operations. This has lower degree and does not add the enormous base_scale coefficient.
- 15 unrestricted integers: degree 813056 L+4184; 1530 operations. This is included as a derivation bridge, dominated by 14.

For each fixed equation, ordinary mathematics formalizable in ZFC proves integer unsolvability equivalent to Con(ZFC). No new end-to-end kernel certificate, consistency proof, global minimum, or global-priority claim is asserted.

## Read and reproduce

- SIGNED_PROOF.md: complete ordinary proofs, definitions, source boundaries and caveats.
- section.tex: self-contained four-page report section (without preamble).
- build_signed.py: standard-library generator, verifying 22 source-file pins before rebuilding.
- check_signed.py: independent scalar evaluator and finite diagnostics using actual compact943 coefficient bytes from ../coefficients/coefficients_compact/.
- generated/signed14.json and signed16.json: explicit division-free arithmetic DAGs with fixed coefficient recipes.
- generated/signed15.json: dominated intermediate.
- generated/LEDGER.json: exact operation counts and symbolic diagonal degree evidence.
- generated/CHECKS.json: 216 actual-coefficient modular comparisons and further diagnostics.
- FIXED_RECIPES.json and upstream/COMPACT_CONSTANTS.json: every nonliteral fixed leaf.
- SOURCE_PINS.json: source URLs, commit, hashes and exact local byte counts.

Run from this directory:

    python3 build_signed.py
    python3 check_signed.py

All generated metadata declares package_root-relative paths. The package root contains INSTANCE.json and the coherent source30 compact943 tuple. The proof text's relative source paths are relative to this signed directory unless explicitly stated otherwise.

## What was combined

Package 29 supplied the 17-integer architecture: a coprime Pell square stack, degree-five intersective merger, and three-root norm. Package 30 supplied the 31-positive-variable quartic, exact index bound, and coherent compact943 tuple. Package 27 supplied the shared-power/h4/Horner evaluation architecture. New steps delete the j guard via a modular Pell orbit, replace a quadratic separation weight by a signed linear one, specialize the base to a cofinal odd-exponent family, and exploit the literal ratio-completeness square witness for omega.

The 14-variable equation uses base_scale=2^kappa, kappa=45933758(5^32+1)+1. This coefficient is an explicit recipe, NOT a materialized integer. Its astronomical binary length is not counted as an arithmetic gate and must not be confused with coefficient-storage efficiency.

New material is AI-assisted and offered under MIT-0. Upstream notices and licenses are preserved under upstream. The frozen support module fast_jones_base.py is derived new-wave code, not a byte copy of an upstream source file.
