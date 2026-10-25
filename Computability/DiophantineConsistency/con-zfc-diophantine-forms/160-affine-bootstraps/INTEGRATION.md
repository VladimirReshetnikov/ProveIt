# Integration into ProveIt

## Suggested placement

The package is self-contained. A suitable first landing point is the dated ZIP in `docs/incoming/`. For an unpacked research contribution, a suitable directory is:

```text
Computability/DiophantineConsistency/con-zfc-diophantine-forms/
  research/affine-parameters-linear-selector/
```

Keep the internal directory names unchanged: the producer and checkers find the retained predecessor at the relative path `inherited_factorial_free/`. A later repository-native refactor can deduplicate this retained material while preserving the pinned source hashes and offline checks.

## Suggested catalogue entry

> **Affine parameters and a linear CRT selector (25 October 2026).** Direct C222 quartics over unrestricted integers: 239 variables / 5,017 monomials, 238 variables / 5,479 monomials, and 237 variables / 14,129 monomials. Every endpoint has degree four and collected coefficient height 7,968. New arguments recover affine horizon/radix/beta signs, use the unsquared growth register for the binomial selector, and reduce the shared Pell frame with a difference of orientation errors. Ordinary mathematical proofs are composed with the retained logical calibration; finite source edits, integral restorations and every collected coefficient have been independently checked. No new end-to-end Lean/Rocq proof is claimed.

## Review order

1. Read Sections 3–9 of the report, especially the signed bootstrap and the new frame's bound `abs(atom)<W`. The stronger old square bound `atom^2<W` must not be imported into the new argument.
2. Check the exceptional Pell anchor branch, the difference-pool error bound and the `t=0` parity contradiction.
3. Inspect `equations/horizon8_difference_frame/source_delta.json` and `frame_certificate.json`. There are exactly seven changed raw rows: 0, 361, 363, 374, 381, 382 and 383.
4. Run `python3 -B verify.py --rebuild`, then `python3 -B -O code/verify_endpoints.py`.
5. Preserve the coordinate ordering and compare hashes before moving or converting equation data.

The compact-support endpoint changes only the selector, radix and beta rows and retains the predecessor's square horizon. Its mathematical scope is narrower; it is useful as an independently reproducible comparison.

## Formalization boundary

The retained logical interfaces are `KEndpoint.c222_iff_zf_refutation` and `ConstructibleChoice.zf_refutation_iff_zfc_refutation`. This packet changes the arithmetic front and finite algebraic compilation, not these interfaces. A good first proof-assistant target is the joint signed bootstrap with affine parameters. Next formalize the generalized LCM selector condition and the coordinate-frame/difference-pool lemmas. Only then connect the frozen raw source to the existing proof-calculus interface.

The release's ordinary theorem, finite verification and historical formalization status should remain separately described in catalogue material.

## Archive integrity

`MANIFEST.sha256` lists every distributed regular file except itself. The root verifier checks each listed digest. The ZIP contains one top-level folder and no symlinks, absolute paths, credentials, compiled Python caches or temporary report logs. The PDF can be rebuilt from the included LaTeX sources, although its metadata may change its file digest.
