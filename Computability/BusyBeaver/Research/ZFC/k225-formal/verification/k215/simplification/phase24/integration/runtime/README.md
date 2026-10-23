# Exact runtime assets

These eight files are byte copies of the owned, source-reviewed tools used for the accepted phase24 check. The three entry points (`build-candidate.py`, `derive_plan.py`, `review_actual.py`) load `phase_adapter.py` and `phase24.json`; the adapter checks and expands the three `phase23-base/` sources. Those bases are the expanded owned phase23 implementations, not external phase22 wrapper files.

The config, source specifications and helper comments retain their preparation-time status text. The terminal receipts in the parent directory and `../../lean/result.json` establish what subsequently ran and passed. Historical absolute paths identify the original inputs. These copies document that run; the leaf `check.py` and `review_actual.py` wrappers are not standalone portable build commands. Running again requires reconstructing the pinned paths and inputs.

No submitted checker, generator or Rocq code was run for this phase. The Lean compiler and owned supervisor are pinned by the check plan and actual review. See [integration records](../README.md) and [accepted check](../../lean/README.md).
