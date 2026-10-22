# Validation evidence

`validation-receipt.json` is the canonical component ledger. Every one of the
51 final module sources must have a successful persisted compiler receipt with
its exact source hash, log hash, and object hash. Object files are not distributed.
The final source pins are in `../source-pins.json` and every retained accepted log
is in `accepted-logs/`.

The check used several resumed compiler invocations in one isolated overlay.
It is not a single uninterrupted fresh 51-module run and does not rebuild the
complete ZFC endpoint. Run `../build.py` to perform a fresh component build in an
empty output directory with no precompiled project objects.

The first 26 modules are recorded by `receipt-0.json`; the remaining modules are
covered by `receipt-provider-tail.json`, `receipt-29.json`, and the later
`receipt-early-recheck.json`; the final facade was checked once more after the
early batch refresh in `receipt-final-recheck.json`. Duplicate accepted module entries are reconciled
by their exact source hashes. The final ledger selects one accepted record for
every module and binds its current retained log and generated object.

`early-check-events.json` preserves the initially observed successful000/001
checks before a later process interruption; it is historical only. Those two
modules were rechecked once to obtain persistent per-invocation receipts before
the final source-bound ledger was completed.

`failed-attempts/` contains resource/configuration failures. None contributes a
proof to the accepted ledger. No accepted module has an unexpected named axiom;
the final five named audits appear in the KResidualSites215 log. The results are
kernel-checked Lean propositions, not conclusions from the diagnostic #eval.
