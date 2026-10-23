# Sparse B4 source compiler for the ten-integer Con(ZFC) equation

This supplement replaces exponential base-five digit positions by a directly
certified four-sum-distinct set. It preserves the pinned 31-variable source
quartic, all four native ports together, and the ten-integer Sun bridge.

Result: one polynomial in ten unrestricted integer unknowns, exact degree
69,554,088,184, with 1,407 binary arithmetic operations (484 additions,
25 subtractions, 898 multiplications) and 79 fixed leaves. The pinned baseline
has degree 589,042,901,992,797,851,562,527,064 and 1,442 operations. Its 851
multiplications are fewer than this circuit's 898; the improvement is in
degree and total operations, not every possible circuit metric.

The new ordinary proof establishes the source coding interface including
unconditional bounds before digit decoding. It retains Sun's 2026 preprint
Lucas bridge and the repository's calibrated compiler endpoint as mathematical
inputs. The checks are finite arithmetic/transcription certificates, not a new
end-to-end Lean/Rocq proof or a proof of ZFC's consistency.

## Reproduce

From this directory, using the Python 3.11+ standard library:

    python3 build_sun_b4.py
    python3 verify_sun_b4.py

The second command checks the actual bound and fixed data, exact coefficient
reconstruction, all 52,360 padded four-sums, the formal norm identity, attained
degree and a literal scalar transcription. The literal comparison uses 120
modular assignments and is a regression test, not a universal identity proof.

`INSTANCE.json` is the active instance. Its coefficient tuple and source
polynomial are unchanged from the baseline. `sources/data/INSTANCE.json`
is immutable historical provenance only; its old dimensions and destination
are not active. `sources/` is a deliberately limited baseline snapshot, not
a standalone copy of the entire repository.

`SUN_B4_PROOF.tex` and `.pdf` give the complete ordinary proof and formula.
`section.tex` is a concise integration section for a larger report, whose
preamble must provide amsmath, amssymb and mathrsfs. `generated/sun_b4.json`
is the explicit division-free circuit. `SUN_B4_VERIFICATION.json` records the
audit, and `SOURCE_PINS.json` records immutable input hashes and references.

The finite-field construction can be reconstructed with `bose_chowla.py`.
It emits the unoptimized largest-gap-translated sequence; `B4_OPTIMIZED.json`
records the later affine multiplier and translation used by this instance.
The active verifier directly checks the optimized weights and does not need
to trust their construction or optimization history.

The native port `beta` and the auxiliary Sun scale `beta_sun = 2^4269882`
are different constants. Do not mix native ports from different tuples.

## Attribution

Sun supplies the ten-integer theorem and Lucas bridge; the pinned repository
supplies the calibrated source quartic, coefficient tuple, quintic finalizer,
and circuit infrastructure. The new contribution is the certified sparse
source encoding, its proof, and its shared fixed-window implementation.
No third-party material is relicensed. See `NOTICE.md`, `sources/NOTICE.md`,
and the upstream notices under `licenses/`.
