# Source provenance and notices

## Pinned repository

Repository: <https://github.com/VladimirReshetnikov/ProveIt>.

Commit: `a2a4cf58c49c745058c40e4a6748d472a3420f18`.

Commit timestamp: 2026-10-10 01:00:30 UTC.

The 25 manuscript chapter files listed in `chapter_manifest.json` and all five archives listed in `incoming_manifest.json` were inspected. Each local source file was checked against its recorded Git blob SHA-1 and byte size before packaging. `source_verification.json` records that check. The source corpus itself is not duplicated in this archive.

The incoming archives include the Distribution Jets, Complementary Depth, Conductor Descent, 10 October Research, and Rigidity reports. In particular, the earlier residual rank results and the completed `S4` certificate were used to prevent duplicate novelty claims.

## Reused exact routine

The file `code/upstream_stieltjes_certificate.py` is a verbatim copy of:

`Analysis/Polylogarithms/docs/reports/stieltjes-derivative-zeros/code/06-zero-geometry-exact_verify.py`

at the pinned commit.

Its SHA-256 is:

`b877ec00a6ac016f937ec7375eea1ca74a0d455dac2c8bf37ad0a994d629f519`.

The new `verify_lerch_boundary.py` replays only the 11 endpoint signs used by the article's proofs. The original routine's authorship and repository provenance are retained; this package does not relicense upstream material.

## Mathematical literature

The article's bibliography gives primary sources and links. The principal externally established analytic inputs are the functional equations and finite rational evaluations of Radchenko–Zagier, and the related functional equation of Choie–Kumar. Their attribution was checked against the primary papers. The recent work of Dixit–Sathyanarayana–Sharan provides context for proposed character-weighted extensions.

The all-conductor beta-symbol Gram theorem and the rationalized Bloch-group facts are used as established inputs from the pinned manuscript, with their exact labels recorded in the integration guide. Classical Hermite–Lindemann transcendence is used only to ensure that a nonzero rational polynomial does not vanish at `-log(2)`.

## Preparation and verification scope

This is AI-assisted mathematical research prepared at the user's request for later repository integration. The principal new arguments received independent internal cross-checks; the delivered programs reproduce the stated finite exact calculations and numerical diagnostics. No external peer review or proof-assistant verification is claimed.

All statements of novelty are relative to the inspected manuscript and incoming reports. The explicit evaluations are proposed additions, with no assertion that every historical equivalent has been excluded.
