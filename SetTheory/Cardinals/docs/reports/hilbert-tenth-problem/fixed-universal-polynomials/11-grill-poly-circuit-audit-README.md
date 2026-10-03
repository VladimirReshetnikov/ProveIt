# Independent full-circuit evidence

Decision and theorem limits: `AUDIT.md`

Executable audit code authored for this review:

- `check_exact_source.py`: exact full-table/full-row/constant/kernel/degree/liveness/finalizer audit
- `check_interfaces.py`: supplementary independent boundary and positive-domain checks

Run each with `python` and `python -O`. The scripts use only standard-library modules. The exact checker reads the pinned producer DAG and literal JSON at the paths identified in `pins.json`; it never executes producer or upstream Python. Normal and optimized receipts are saved as `exact-normal.json`, `exact-optimized.json`, `interfaces-normal.json`, and `interfaces-optimized.json`.

`sources/` contains inert reviewed text and JSON, including upstream `.py` files read for formula/template inspection only. Do not run them as part of this audit. `source_connector_pins.json` authenticates twelve independently fetched upstream files at the fixed commit. `pins.json` authenticates thirty-two dependencies. `MANIFEST.json` seals the audit artifacts themselves.

The full source passed exact replay in 9.289 seconds normal and 9.158 seconds optimized in the final observed run. No complete Pell witness or actual universal input was materialized.
