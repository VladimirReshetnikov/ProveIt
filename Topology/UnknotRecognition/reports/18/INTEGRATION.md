# Integration into ProveIt

The patch is relative to the contents of
`Topology/UnknotRecognition/fast/` at revision
`ea2abcb115aaa58f0b193ce1e045c2def983e1e6`.
The unmodified source is retained under `reference/fast/`; the desired result
is the package's `fast/` tree.

## Apply from the ProveIt repository root

```sh
git apply --check --directory=Topology/UnknotRecognition/fast /path/to/package/integration.patch
git apply --directory=Topology/UnknotRecognition/fast /path/to/package/integration.patch
```

Then run the repository tests from `Topology/UnknotRecognition/fast`:

```sh
python -m unittest discover -s tests -v
```

The delivered patch was applied in a temporary repository with exactly this
directory layout. Both `git apply --check` and `git apply` succeeded, and the
complete patched tree was byte-identical to the delivered `fast/` tree.
`results/patch_check.json` records the check. No baseline file was removed,
and the existing MIT-0 license was unchanged.

If the target revision has moved, review the source changes before resolving
patch conflicts. The pinned patch check is evidence about the recorded
baseline, not a compatibility claim about arbitrary later revisions.

## Exact source mapping

All paths below are relative to `Topology/UnknotRecognition/fast/`.

| Path | Change and purpose |
|---|---|
| `fastunknot/braid_profile.py` | New direct structural certificates for word and signed-run braid input; diagnostic dominated signature routine and witness checking. |
| `fastunknot/twist/tail.py` | New exact one-run recurrence and compressed degree-profile API. |
| `fastunknot/twist/streaming.py` | New degree-streamed exact homology, explicit live-storage budgets, and optional finalized-rank early rejection. |
| `fastunknot/twist/continuation.py` | New explicit RLE research frontend selecting tail, streaming, or ordinary macro evaluation. |
| `fastunknot/recognize.py` | Add opt-in `use_braid_profile=False` parameter and direct checked-source structural stage. |
| `fastunknot/__main__.py` | Expose the opt-in `--braid-profile` switch. |
| `tests/test_braid_profile.py` | New structural certificate and production integration checks. |
| `tests/test_twist_tail.py` | New recurrence, independent-cube, huge-exponent, and resource checks. |
| `tests/test_twist_streaming.py` | New enumeration, compact-map, homology, storage, and early-exit checks. |
| `tests/test_twist_continuation.py` | New raw frontend schema, parity, exactness, resource, and exit-code checks. |
| `TWIST_CONTINUATION.md` | New detailed research frontend and API documentation. |

The production recognizer's existing default behavior is retained. The new
production source-braid structural path is explicitly enabled by
`--braid-profile` or `use_braid_profile=True`. Tail and streaming are additive
research backends; the existing `backend="twist"` production option continues
to use its established adapter.

## Archive the research material

The article, raw results, audits, and reproduction tools can be archived at
`Topology/UnknotRecognition/research/twist-continuation-20261008/` or another
repository research location. They are not applied by the source patch.
Keep the baseline revision and raw result provenance with the article.

To regenerate and recheck the patch from this package:

```sh
python tools/make_integration_patch.py
```

This compares `reference/fast/` with `fast/`, excludes Python caches, preserves
the license, applies the resulting patch to a fresh temporary repository,
and verifies complete byte equality. It does not repeat the full tests.
