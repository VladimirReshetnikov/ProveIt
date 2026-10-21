# Source159 selected replay and saved-record review

`run.py`, `secondary_blank.py` and `review_saved.py` are the exact root-executed
runner, independent secondary blank driver and independently executed saved
auditor. Their bytes have not been adapted for publication; each already takes
explicit input/output paths. No submitted checker was changed.

Use the [reproduction guide](../../intake-197-reproduction.md) for complete
commands. `prepare_audit_view.py` only expands the saved-file index, preserving
the exact outputs and selected current input snapshots needed by the unchanged
auditor. It executes no candidate. The original review explicitly lacks a
historical before/after hash map; the prepared view does not create one.

`publication-writer.py`, `candidate-publication/` and `reviews/` retain the
historical publication/source-review authors' scripts and their original paths.
They are provenance, not additional replay commands. The selected fresh runner
has eight90-second finite jobs and two parallel360-second full runtime jobs.
Its mathematical acceptance requires the semantic records, not exit codes alone.

Stored C++ receipts are delivered evidence only. No manifest wrapper, ancestor
suite, optimizer, compiler or proof assistant is invoked by these commands.
