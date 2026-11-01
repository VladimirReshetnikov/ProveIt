# Fourteen-variable six-edit source candidate

This source-only capture contains 995 regular Lean source files. Of these, 984
come from the frozen six-edit 13-variable candidate and 11 from the earlier
frozen 14-variable extension. The source hashes and the shared explicit import
lists were checked, and the workspace matched the 995 candidate sources before
and after capture. The observed Git HEADs and input hashes are in the manifest.

The 11-module source order is inherited from the earlier prospective survey.
The separate `check_dependency_inheritance.py` check composes the prior Lean
`--deps` receipts by source hashes and import lists: 978 unchanged shared
files, six edited shared files, and 11 extra files. Its zero-exit receipt SHA is
`f4ab988ab0e3349a637dc206136f370f71c757f59b59f7c5bd73db34c5b1cb6c`.
It validates the recorded receipts and their input hashes; it does not rerun
Lean or authenticate an object environment. A matched 107-module parent,
retained-origin checks, external companion guards, and a guarded 14-variable
successor and independent comparison are still required. Any later workspace
drift must be recorded.
The 848-project ancestor remains author-only and package-transitive/dynamic
ancestry remains inherited.

The source-capture process exited zero. Manifest SHA-256:
`34853467677165ab413e383ca9d67560cc3e44c57ebdf5b1cbce870996365aae`.
