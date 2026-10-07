# Sources and attribution

## Pinned mathematical interface

The four raw Lean source files are pinned at commit `17f048dfa919de04a1989035a2d680ec0865c774` in `VladimirReshetnikov/ProveIt`. They preserve exact bytes, including original line endings; no text decoding/re-encoding normalization was applied to the snapshots. Each was verified against its Git blob SHA-1, which is SHA1("blob " + decimal byte length + NUL + raw bytes).

The exact input concerns the Prop-valued catalogue definition `lemma_16_10`, not an asserted Lean theorem. Its modulus assumption is only nonzero N. The actual numbered Lemmas 16.6 and 16.9 have prime-modulus assumptions; Report 286 claims their recorded algebraic/selection predicates over composite N and constructs the all-box line cover directly, without applying those numbered results there.

### Definitions.lean

https://github.com/VladimirReshetnikov/ProveIt/blob/17f048dfa919de04a1989035a2d680ec0865c774/Combinatorics/Ramsey/Lean/GowersSzemeredi/Definitions.lean

- Git blob SHA-1: 97113b7afa6925a2dd4b76641eeaeff09597ab6a
- Raw bytes: 15504
- Raw SHA-256: 17241a9ffa53e2c6b335eb326920952a7f3da25e5e5a601a7aca5606462f5e4b
- Snapshot: provenance/sources/Definitions.lean

### Section10.lean

https://github.com/VladimirReshetnikov/ProveIt/blob/17f048dfa919de04a1989035a2d680ec0865c774/Combinatorics/Ramsey/Lean/GowersSzemeredi/Section10.lean

- Git blob SHA-1: 302e8a223f56dcdabf29f30ca3c80ac62a7adbfc
- Raw bytes: 24924
- Raw SHA-256: 8b63d784485ba8291b614a9153399cae216d2adaf37c9770344521083523cb2d
- Snapshot: provenance/sources/Section10.lean

### Sections14_15.lean

https://github.com/VladimirReshetnikov/ProveIt/blob/17f048dfa919de04a1989035a2d680ec0865c774/Combinatorics/Ramsey/Lean/GowersSzemeredi/Sections14_15.lean

- Git blob SHA-1: 5d91dce37bbca59fc76dfd30ec3a485d72ba583c
- Raw bytes: 20864
- Raw SHA-256: cc7782c87e1e6261b744f13b7fd62082efcb1b6b45a24a31e694a915ebe6c13b
- Snapshot: provenance/sources/Sections14_15.lean

### Section16.lean

https://github.com/VladimirReshetnikov/ProveIt/blob/17f048dfa919de04a1989035a2d680ec0865c774/Combinatorics/Ramsey/Lean/GowersSzemeredi/Section16.lean

- Git blob SHA-1: c5c7d2bee91bc589de1d3082429f7ee3597e99f9
- Raw bytes: 43323
- Raw SHA-256: be20dcf52ba6cb0bc54a03c194ad9b64f486562be032eccf788f14e97e1e65ed
- Snapshot: provenance/sources/Section16.lean

`Definitions.lean` supplies the exact proper progression, box, partition, width, affine and multiaffine conventions. `Sections14_15.lean` supplies the all-family weighted product property and arrangements. `Section10.lean` supplies `HasBohrDifferenceModel`. `Section16.lean` supplies all quantitative controls and named data.

## Upstream source 50

Title: Sharp Branch-Cover Profiles and a Counterexample to the Two-Input Form of Lemma 16.10. Research manuscript prepared for the ProveIt project, 6 October 2026.

https://github.com/VladimirReshetnikov/ProveIt/blob/8c40adc24df2e6f338cea728887772aead4bf144/docs/incoming/ramsey_branch_cover_obstructions.zip

- Archive Git blob SHA-1: 807facdac4171f57887a5d5b8affe2427a610a4f
- Archive raw bytes: 517479
- Archive SHA-256: 0282f4e9a073a71e4ebe58c9e37a68c2daa3bb7af5a87b0f6773df3a264e10de
- Original archive member: ramsey_branch_complexity/article.tex
- Member raw bytes: 82816
- Member SHA-256: 792866e778a4bba567913d9961ad0948b1409457e4b989343a0db70993beba6a
- Preserved snapshot: provenance/sources/source50_article.tex

The archive pin is `8c40adc24df2e6f338cea728887772aead4bf144`. The same archive blob is also present at the earlier inspected arrival pin `b6a8ee96631fa845067e9ec9e5b1c2f42960a9c9`. The included article was checked byte-for-byte against the named ZIP member. Its SHA-256 is a member identity; the archive Git blob SHA-1 is not a Git-file identity for that article.

Source 50 already proves the prime-field two-input counterexample, finite-alphabet root bound and cover envelope, optimizer rigidity from a strict symbol-mass gap, progression-balanced words, a growing-alphabet avoidance theorem, and the full-domain prime-field gamma=1 endpoint characterization. The relevant original line ranges are 257–317 (finite list mechanism), 669–777 (growing alphabet), 810–1134 (two-input construction and interfaces), 1136–1204 (endpoint), and 1527–1533 (torsion question).

Report 286 reuses and credits that finite-list mechanism and endpoint argument. Its new contribution relative to these local sources is the sparse weighted restoration barrier with the exact named-data realization, together with progression-local affine avoidance for a short interval alphabet over every cyclic modulus. It gives only a restricted affirmative development of the torsion question. Standard elementary concentration inequalities and the weighted-energy observation are not claimed as original discoveries. No comprehensive priority investigation was performed.

## Upstream source 49 as a comparison

Title: Second-Order Degeneracy, Dual Uniformity Bounds, and an Acyclic Model Theorem. Research manuscript prepared for Vladimir Reshetnikov with ChatGPT, 6 October 2026.

https://github.com/VladimirReshetnikov/ProveIt/blob/b6a8ee96631fa845067e9ec9e5b1c2f42960a9c9/docs/incoming/gowers_rank_dual_refinements.zip

- Archive Git blob SHA-1: 29f2d39e439ed6c4349054c6c1b18ce78e762057
- Archive SHA-256: 960c7e1ea81f2f9e80f9512bee3af1333fd62677a89cb728f06d2b92faff34a8
- Original member: gowers_rank_dual_refinements/gowers_rank_dual_refinements.tex
- Member SHA-256: 0dd5bbd7f35ac0309f0bfe2f3673e5823bec3dbebd75d74924b6b2f2a20f0bcd
- Relevant section: original lines 1890–2870, especially Theorem `ac:thm-main`

The archive and member bytes were inspected during preparation. The paper already supplies a conditional acyclic retained-core theorem from seven interfaces, with the global core chosen before the local loss. It is cited for the comparison and quantifier boundary only; no result from it is used as a proof dependency in Report 286. It is not bundled.

## Published framework

W. T. Gowers, A new proof of Szemeredi's theorem, Geometric and Functional Analysis 11 (2001), 465–588.

https://doi.org/10.1007/s00039-001-0332-9
https://sites.math.rutgers.edu/~zeilberg/akherim/GowersMasterpiece.pdf

The original journal page 567 was visually checked for the nested c, q and s controls. Journal page 575 was checked for the closing graph-count comparison; its dimension-k left side is not silently identified with the edited repository transcription's different same-dimensional formula. Report 286 concerns the explicitly pinned interface and makes no claim against the full contextual theorem or a global Szemeredi bound. The primary paper is not redistributed.

## Reproducibility and representation identities

`provenance/source_manifest.json` is the machine-readable receipt for the five included snapshots. Each records raw byte count and SHA-256. The `canonical_base64_sha256` field is SHA-256 of RFC 4648 base64 encoding of the raw bytes, with no whitespace or final newline. It is a defined alternate representation, not a retained original network-transport receipt. The companion verifies both representations, round-trip equality, and the four raw Git blob hashes.

The omitted archive's hash and the article's archive-member metadata record preparation-time evidence. Offline replay verifies the included member digest; it does not re-open or independently fetch an omitted archive. SHA-256 identities are integrity checks, not author authentication or publication certificates.

## Implementation lineage

The guarded builder and builder-regression suite are adapted from Report 285's frozen candidate v1 without changing that report. They retain exact inventories, no-follow filesystem access, exclusive output creation, bounded subprocesses, controlled environments, deterministic ZIP metadata, optimized-mode parity, and source immutability checks. No unrelated Report 285 source evidence or mathematics is carried into this package.
