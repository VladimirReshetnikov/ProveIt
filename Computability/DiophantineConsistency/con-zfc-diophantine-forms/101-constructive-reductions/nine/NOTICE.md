# Attribution and provenance

The radix-position normalization, recalibration, new composed circuits, exact named-register verifier and accompanying exposition were developed with OpenAI assistance for Vladimir Reshetnikov in this research iteration.

The saturated positive Pell theorem and 333-term full-radical majorant are inherited from `ConZFC_Saturated_Certificates_2026-10-24.zip`; the compact54 coefficient recipes and additional calibration documents are inherited from `con-zfc-saturation-and-projection-2026-10-23.zip`. Both archives were read at ProveIt commit `7e533c33819ee1f703b69f2778a767cdc069940d`. Their hashes are recorded in `SOURCE_PINS.json`.

`build.py`, `circuit.py`, `poly.py`, and `exact_audit.py` are derived from the first archive's corresponding nine-variable code, with explicit changes for the new layout and evaluator. `verify.py`, `normalization_check.py`, and `verify_coefficients.py` are authored for this component. Retained source licenses and notices are under `licenses/`, `native_original31/licenses/`, and `compact/provenance/licenses/`.

The preserved material under `inherited/` and `compact/provenance/` describes its original constructions and historical relative paths. It is included as proof provenance, not as an assertion that every old command is an entry point for this packet. The supported release commands are the five root-level check/build commands in `README.md`.
