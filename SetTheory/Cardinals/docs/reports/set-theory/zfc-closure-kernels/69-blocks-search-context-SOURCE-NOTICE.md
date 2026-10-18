# Source and attribution boundaries

This directory contains new search drivers and research evidence derived from the frozen context246 and beyond252 archives in ProveIt's incoming research material. It does not claim authorship of the inherited machine, register program, compiler or proof scripts, and does not impose a new blanket license on imported or derived material.

- `../../reference/context246/` contains the frozen reference material from `docs/incoming/zfc-context246-20261018.zip` at ProveIt HEAD `8cdc55ff9281b0aaba49bf74b0b225d57f12b893`. Its own notice, provenance, checksums and source license boundaries apply.
- `decoder_entries.json` is copied from `beyond252/exploratory/historical/decoder_entries.json`.
- `rotate_search.py` and `dag_tools.py` derive from `beyond252/exploratory/vendor/`. The closed-sequence transformations and structural source reader are inherited algorithms, included so the new drivers can replay the searches without the rest of that archive.
- The packaged `rotate_search.py` and `dag_tools.py` remain byte-identical to the copied inherited files. Their standalone readers retain the original explicit source-root convention; the packaged search drivers obtain the frozen source through the shared common module.
- The new drivers and `search_common.py` use package-relative imports and reference paths. These portability adaptations do not change the attribution of inherited algorithms. In `rotation42_congruence.py`, the package path is `ROOT`, the shared code directory is `code`, and the source-DAG root is the separate integer `SOURCE_ROOT`.
- `sites.txt` and `../../data/neutral_rows.txt` were generated during this research by the runtime-analysis teammate from the exact context246 table and pinned register source. They are data inputs, not proof-assistant certificates.
- The exact register source `../../reference/context246/sources/Prog254.v` has SHA-256 `1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746`.
- The old-label table `../../reference/context246/machine/zfc_prefix246_old.tm` has SHA-256 `303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee`.

Mira-Cult designed the original 254-state machine; Jeff Ketchersid supplied the referenced Coq proof; subsequent ProveIt work supplies the register permutation, runtime folds and calibration. No new end-to-end proof-assistant endpoint is claimed by this directory. Every changed-source table in this directory is an initialized-runtime artifact; its blank initialization has not been verified.
