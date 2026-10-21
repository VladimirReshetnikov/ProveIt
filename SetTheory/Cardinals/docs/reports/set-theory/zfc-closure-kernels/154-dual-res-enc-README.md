# Encoding research replay bundle

This directory accompanies the 218-state research report. It contains two independently checked **219-state** MP variants and exploratory encoding/source searches. It contains **no verified machine with 218 states or fewer**. Read `final_encoding_summary.md` for exact search scopes and proof status; the two `.tex` files are sections of the main report.

## Prerequisites and working directory

Use Python 3.10 or later. The closed-grammar parser and equality synthesis additionally need a C++17 compiler; the default examples use `c++`. No third-party Python packages are required for these encoding scripts. To build the report sections, use the main report's LaTeX wrapper and a TeX installation with `amsmath`, `amssymb`, and `hyperref`.

Run commands **from this directory**, preferably in a writable copy. Scripts create or overwrite generated experiment subdirectories beside their pinned inputs, and some imports create small support directories. They do not modify the pinned `K219_Construction_2026-10-20`, `K220_Construction_2026-10-20`, or `K221_Construction_2026-10-20` inputs. `ENCODING_WORKSPACE` may point to another fully provisioned copy of this bundle. Some older scripts also accept `--workspace` or explicit source/table paths; see their `--help`.

## Representative replay

```sh
c++ -O2 -std=c++17 closed_parse.cpp -o closed_parse
python3 rebase219.py
python3 inverse_mp.py
python3 inner_parity_codec219.py
python3 disequality_codec219.py
python3 disequality_dual219.py
python3 split_bundle219.py
python3 split_bundle_corrected219.py
python3 source_facts219.py
python3 semantic_subtree219.py
python3 disequality_inverse219.py
python3 shifted_even_inverse219.py
python3 dyadic_pairing219.py
```

The detailed summary lists the complete command sequence and required precursor experiments. The `6^8` row censuses and `9!` register sweep are larger jobs; the register sweep emits a large per-permutation JSON. Compact recorded receipts are under `receipts/`; generated tables with only a compiler-count receipt must not be treated as verified machines.

The two checked 219-state MP sources/tables are in `inputs/k219_no_push_copy/` and `inputs/k219_no_push_cache/`. Their small symbolic-runtime and blank-startup summaries are named `receipts/verified_k219_*`; the enclosing report's machine directories hold the full case certificates and canonical tables. Other selected source inputs are retained for reproducibility, with their limitations stated in the receipts.

`sha256_manifest.json` identifies every delivered file except the manifest itself. `receipts/portable_validation219.json` records a clean-copy replay, `receipts/portable_inverse_addendum.json` records the two final codec replays, and `receipts/latex_validation219.json` records a standalone section build. The `theory_audit/` directory contains the separate positive-equality T/B countermodel audit and its literal native-AST checker.
