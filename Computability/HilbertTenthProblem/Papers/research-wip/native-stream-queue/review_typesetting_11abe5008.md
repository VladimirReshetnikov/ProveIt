# Bounded semantic-transfer review of 11abe5008

Reviewed commit `11abe50082d5e031c862a638e7e1b4e649b3d906`, adding Parts IV–VI and their appendices to `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/quadratic-orthant-certificates`. The mathematical transfer passes. Two narrow editorial corrections are provided in `review_typesetting_11abe5008.patch`: one domain qualification in the README, and an inaccurate description of the sole compiler-text difference. No original compiler, export, archive or receipt was changed or executed.

This review covers the three newly assembled manuscripts, the explicitly deduplicated reset passages, and their new comparisons, domain qualifications and provenance. It does not re-review historical Parts I–III, rerun unchanged author suites, inspect PDF layout, or apply to future revisions. The typeset PDF remains the delivered artifact; the patch changes only README/TeX text and does not rebuild it.

## Findings and narrow patch

1. **README lines 43–46 overstate real exactness.** The blanket assertion that source 17's certificates have only natural zeros over the nonnegative reals excludes its own all-duration variant. The original and preserved article section, lines 5267–5280, explicitly gives the counterexample: take the natural source/peak witness at `h=328`, `H=11`, `B=6`, `v_h=14`, whose minimum duration is `388`; at the natural parameter `N=389`, the padding coordinate `z=1/2` makes the final square vanish. A natural padding coordinate cannot do so. The checker independently evaluates this exact rational residual. The extension to the complete certificate follows because all other coordinates and terms are unchanged from the already proved source/peak witness; this review does not replay that large witness. The patch restricts the introductory claim to minimum-duration and trace certificates and states the natural-only padding exception. The source theorem and the article's later warning were already correct.

2. **README lines 54–55 and 137, article line 4880 misidentify emitted metadata as a docstring.** The sole textual difference between reset `source_quadratic.py` and membrane `direct/quadratic_core.py` is `reset-trace` versus `membrane-trace` in the returned packet's `scope` string at source line 89. It is not a Python docstring. The arithmetic, source construction and count expressions are otherwise literally identical. The patch changes the three descriptions to “one word in the emitted scope metadata.” This does not alter the mathematical reuse or claim byte equality of the differing compiler outputs.

The patch has three README hunks and one TeX hunk. Exact old-context checks and an independent line-by-line hunk application reproduce the expected corrected bytes. A second replay using the external `patch` utility on a private copy also passes. The corrected README SHA-256 is `5bc5fb11f1750567a2bbdd60b1d2fa0e99107c1b2d297f9c7e3ae0e5f506777a`; corrected TeX SHA-256 is `35fdfbe66978c33a3b42956bea404f034f6d6e52fb52dcd5776ccfd23ef67145`.

## Occurrence-preserving transcription census

The checker authenticates the original ZIPs and the new/previous TeX and README blobs. It matches each original block to at most one target occurrence of the same environment, restricted to that manuscript's new Part and corresponding appendices. Repeated blocks require repeated target occurrences; a source-16 passage cannot silently count as a copied source-17 passage. The receipt stores source and target occurrence indices, lines, and normalized hashes.

Normalization removes comments, whitespace, label declarations, citation/label namespace prefixes, and display-layout commands. It maps only the documented macro-name clashes (`zero`/`mmzero`, `ind`/`rnind`, `code`/`rncode`). All 28 source-specific mathematical/notation macro definitions are independently compared; the `file` rendering helper is excluded from mathematical macro checks. This is a constrained textual comparison, not a full TeX parser or proof assistant.

| Original source | Labels preserved | Displays exact | Formal statements exact, including unlabelled | Proofs exact | Tables exact |
| --- | ---: | ---: | ---: | ---: | ---: |
| 15, membrane motifs | 37 | 29/29 | 8/8 | 9/9 | 1/1 |
| 16, literal universal membranes | 35 | 42/42 | 10/10 | 9/9 | 7/7 |
| 17, reset Petri nets | 34 | 42/45 | 15/15 | 11/13 | 9/11 |
| Total | 106 | 113/116 | 33/33 | 29/31 | 17/19 |

All three abstracts, all 11 literal listings, and the motif diagram are also preserved after the stated normalization. Tables include the two longtable appendices. These totals are **not** a claim that every source-17 occurrence is reprinted: its seven unmatched blocks occur in the four explicitly declared deduplicated passages below.

## Declared deduplication: supported mathematical reuse

The new reset chapter expressly replaces four passages with pointers into source 16. I checked the actual omitted statements/proofs against the surviving source-16 constructions, their domains, and the authenticated program files.

- **TM table:** all 30 state-symbol entries agree; the 29 defined rules are identical and `J1` is the sole undefined entry. The typography changes from compact `0RB`/`halt` to `(0,R,B)`/`undefined`; the checker parses and compares the entire two-column state table rather than treating it as a copied occurrence.
- **Counter-macro proof:** the omitted proof establishes pop invariant `X=2(Q-k)+r`, scratch `T=k`, the decreasing natural rank `Q-k`, pop cost `5Q+r+2`, push invariant `Y=Y_0-k`, scratch `T=2k`, and cost `7Y_0+2+w`. Source 16 retains those invariants with scratch `K`, the same total `5Q+r+7Y_0+w+4`, and the required scratch-zero boundary predicate. Thus all natural half-tape values remain covered; finite source-table checks are not substituted for loop termination.
- **Source-fiber proof:** the preserved source-16 theorem is for the same deterministic 528-row program when `d=3`, with 761 semantic branches and 233 omitted zero-test bases. Its globally nonnegative strong gates force exactly one selector even over nonnegative reals, then inactive bases vanish, natural inputs propagate natural active bases, and HALT has no outgoing row. These are exactly the omitted reset proof's uniqueness, real-to-natural and first-halt premises. The printed reset proposition and full construction remain present.
- **Prime-macro descriptions and cost table:** the three omitted displayed formulas become `A=N-k, B=pk`, `(3p+1)N+2`, and `A=N-pk-j, B=k, 0≤j<p` under the explicit counter/loop/remainder renaming. The two division cost rows agree term by term under `n→N, s→r`: `2Q, N+Q, 2, N+3Q+2` and `N+Q, N+Q, 2, 2N+2Q+2`. The surviving proof covers every positive raw prime-coded input, preserves the coprime cofactor and other exponents, clears scratch before TM simulation, and restores the physical scratch at each cut. Reset-specific rejection of input zero and the net/physical-peak results are still printed.

The checker also proves exact byte equality of six paired virtual/physical program files, and exact text equality of the two source compilers after the single emitted-scope word replacement. It authenticates the two omitted reset proof notes and their source-16 counterparts. With lowercase word-token 8-grams, occurrence coverage is `631/693` and `1527/1552`, rounding to the stated 91% and 98%. These similarity percentages are provenance evidence; the mathematical reuse is justified by the explicit invariant and theorem comparisons above.

## Editorial scope and arithmetic transfer

The new editorial comparisons are supported, subject to the two corrections above:

- Motif certificates require a well-formed finite schema and natural witnesses. Completeness is existential in the schema, not completeness for every preassigned catalogue. The quadratic residual equations yield a quartic SOS; they do not inherit the real-to-natural property of the strong quadratic selector gates. Only the derived coordinates are unique after the source and decorated schedule have been fixed.
- The direct and prime membrane constructions retain the literal universal source, both raw half-tape inputs, the correct scanned-symbol/control convention, and exact global quiescence. Their outcome polynomials certify externally specified counter-instruction horizons, not supplied membrane birth histories. Ordinary program-to-half-tape preprocessing remains external. The huge prime example is derived from proved macro costs, not asserted to have been executed.
- Reset exact acceptance remains DONE with all other places zero, not coverability or arbitrary deadlock. Consume–reset–produce order, debt, fuel threshold and the exact duration formula are retained. The source horizon `h` and arbitrary reset-trace horizon `N` are different external compiler parameters. Shared-reset marker states still require their trace-level coordinates; canonical decoded outcome certificates do not claim those markers can be discarded from arbitrary traces.
- The newly mentioned forced-first-step projection is correctly marked as an unimplemented bounded graph projection. Its counts are `2811(T−1)` witnesses, `5(T−1)+1` squares, and `761(T−1)` products, with the terminal comparison retained even at `T=1`.
- The previously reviewed reset gate weakening `(E−e)(e+X) → (E−e)X` is correctly natural-only, on the same coordinates and with the same canonical uniqueness. Its off-zero correction is `Σ_j(E_j²−Σ_t e_jt²)`, so this is not polynomial equality. Its specified complete sparse schedule saves `761h` additions: `12770h+11 → 12009h+11`; no source-independent optimality or fixed-arity universal bound is claimed.

The assembled Parts' arities still grow with schemas/horizons. Their semilinear fixed-horizon projections and universal substrate simulations therefore do not establish a new fixed-arity universal Diophantine equation. No new unsupported arithmetic theorem was found in the editorial comparisons. The unchanged malformed-input API defects recorded in the reset review remain explicitly disclosed; the placement did not silently apply the patch.

A second bounded editorial reader independently agreed with the real-exactness finding and checked the strong-gate dependency, schema scope, source table/input/counts, reset debt and marker invariants, external horizons, natural-only reduction and unimplemented prefix projection. Their [note](review_qoc_typesetting_editorial_11abe5008.md) has a separate [source-pin record](review_qoc_typesetting_editorial_11abe5008.json), SHA-256 `1ffeb6c879ecbaf19e95a2f6a3ae405e5685f21b770fb07c8d41f41b40ee2b64`. That reader did not review the later-discovered docstring-versus-metadata distinction.

## Pins and reproduction

The portable helper reads immutable Git blobs, not the mutable working tree, and opens archives in memory. It verifies all 184 archive-member pins against the authenticated placement inventory and compares all 124 maintained companion paths at the typesetting commit byte for byte. These cover 128 original member paths because same-package duplicate receipts/data have shared placements. Cross-package equal files are recorded separately as deduplication evidence, not counted as reset-package placement.

| Input | Revision | SHA-256 |
| --- | --- | --- |
| Added `article.tex` | `11abe5008` | `b8b0fee6cf065e1f2cb6e37c8ac0ef595589b8853de107a13b81e1c68418bc27` |
| Added `README.md` | `11abe5008` | `1ea9b167e8ce3efb9034b42da9f31ace996fa8d376c1265dd5ccf7a276dbc299` |
| `Membrane_Motif_Research_Package.zip` | `2a8a39599` | `47da14f271cccfb16fceb5cec859889a02d14e6ff5c23ca121f6f17a1ac98e99` |
| `Universal_Membrane_Research_Package.zip` | `2a8a39599` | `dc4fe8f07c278614d567029e40bbdf2db2326e5ea4b04f423bcc3b0b2610e3b5` |
| `Reset_Petri_Net_Certificates.zip` | `aebfa386e` | `b1efbc90aac106061e93ffc92adda686b8e1b9f57539aae976bf227dffec83e3` |

The receipt includes both previous TeX/README pins, every archive member, the original review notes at `85294a527` and `9df1f72ca`, and placement inventory at `653349f6a`. These fix the evidence for this revision without claiming to audit subsequent changes.

From any directory, with `REPO` set to a checkout containing those Git objects:

```sh
python /path/to/review_typesetting_11abe5008.py --repo "$REPO" --expect /path/to/review_typesetting_11abe5008.json
```

The writer form uses `--write receipt.json --patch correction.patch`. The Python API is `verify(repo) -> (receipt_without_checker_self_hash, patch_text)`. It performs no writes and executes no archived code. The command-line saved-receipt comparison is type-sensitive, including numeric types, and remains active under `python -O`. A fresh replay from `/tmp` passes with the saved receipt unchanged.

The core review artifacts are: `review_typesetting_11abe5008.py`, `.json`, `.md`, and `.patch`. The separate editorial note and pin record are also retained. Scratch extraction, temporary analysis scripts and private patch copies are not part of the maintained packet.

Root read the helper, the declared deduplication evidence and both findings, regenerated the exact saved receipt, and applied the published patch using `git apply` to fresh private copies. Both corrected hashes matched. The maintained report text and PDF remain unchanged; applying the TeX correction requires a PDF rebuild.
