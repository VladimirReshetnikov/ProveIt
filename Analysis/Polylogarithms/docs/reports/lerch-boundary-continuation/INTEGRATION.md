# Integration into ProveIt

## Suggested destination and retained sources

Retain this complete report package under a new directory such as:

`Analysis/Polylogarithms/docs/reports/lerch-boundary-geometry/`

Keep `article.tex`, the compiled PDF, the exact certifiers, the generated rational endpoints, the provenance record, and the explicit limitations together. No existing certificate or attribution should be removed.

## Additive chapter

`integration/09-lerch-boundary.tex` contains the full research content, with labels and bibliography keys prefixed `lerchbd:`. Its only new mathematical macro is `\LBf`. It is intended to follow `\input{chapters/09-zero-geometry}` and precede the Herglotz chapter. The namespaced bibliography fragment is to be input inside the existing bibliography.

The chapter uses `tabularx`, which the pinned manuscript preamble does not load; the guarded installer adds that package. Other macros and theorem environments are already present in the inspected manuscript. The chapter was smoke-tested with a book-class harness using the required manuscript-compatible macros; **the entire remote consolidated manuscript was not rebuilt**.

For maximum editorial economy, one can instead merge the sections into the existing zero chapter using the mapping below. The standalone PDF remains the authoritative complete delivery.

| Standalone article label | Proposed placement / source dependency |
|---|---|
| `thm:n2count`, `thm:n2shape` | Following `zeros:thm:n1brackets`; extend beyond index one. |
| `thm:abel` | After the master identity or in the finite spectral-jet discussion; retains classical Lerch attribution. |
| `thm:regularity`, `thm:rootregularity`, `cor:alternating` | New subsection on the singular endpoint rho=1. |
| `thm:eventual` | After `zeros:thm:zeroasympt`; supplies mixed derivative estimates absent from an undifferentiated remainder. |
| `thm:weak`, `cor:k1collapse` | After the existing remark on repeated elementary endpoint roots. |
| `thm:fold` | Following low-index endpoint certificates and weak-deformation geometry. |
| Certificate implementation and data | A new report verification subdirectory; do not overwrite historical certificates. |

In the additive chapter these labels become `lerchbd:thm:n2count`, etc.

## Guarded local installer

The installer is **dry-run by default**, does not access the network, and rejects a mismatch against the inspected source blobs. From the unpacked package:

```sh
python integration/apply_integration.py --repo /absolute/path/to/ProveIt
```

Review the printed diffs. Only an explicit `--apply` causes local writes:

```sh
python integration/apply_integration.py --repo /absolute/path/to/ProveIt --apply
```

The program validates all anchors and destinations before starting writes. It adds two files and edits the manuscript main file, its bibliography wrapper, and the monotonicity research paragraph. It refuses to overwrite the two added-file destinations. It is designed for a clean local working tree at the inspected file versions; it does not commit, push, or create a pull request.

When the repository has moved on, review `integration/edits.json` and merge the exact semantic changes manually rather than bypassing the blob guards. The full package itself is not copied into the repository by this installer.

## Proposed research-question replacement

The old paragraph says that higher-branch monotonicity is suggested by the first correction and proved globally only at index one. Replace it with a statement distinguishing two facts: sufficiently large derivative order gives decreasing motion throughout the deformation, whereas small derivative orders have turning points, alternating endpoint directions, and births of zero pairs. The exact source and replacement strings are in `integration/edits.json`.

This is an update to a research question, not a retraction of an existing proved theorem. The sharp C^(k-1) endpoint regularity should accompany any new claims about parameter derivatives.

## Review checklist

Replay the exact certifiers and inspect the ordinary proofs before accepting the new theorem statements. Preserve the distinction between the certified minimum-parameter interval and the longer diagnostic decimals. Keep the unique index-three fold claim restricted to its specified inner gap; the possible absence of additional outer folds remains a conjecture. Rebuild the full manuscript after integration and check namespaced references, chapter numbering, and bibliography layout.
