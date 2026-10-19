# Portable quick reproduction

This is an actual separate execution of the delivered `code/verify_all.py` quick path after packaging and explicit assertion-guard hardening. The command reconstructed both tables and checked byte identity with the delivered machine files, then reran both blank interpreters in both numberings and all 8,390 finite instruction fixtures. `verification.json` records commands, exit codes, durations, and before/after bindings for the delivered machine, code, and reference inputs.

This quick path did not repeat the roughly six-minute expanded replay. That complete earlier replay is recorded in `../expanded-runtime.json`; all its 291 reference inputs and algorithm body were preserved, with filename/guard adaptations recorded in `../packaging-adaptation.json`. Historical absolute paths in the logs identify the actual execution location.
