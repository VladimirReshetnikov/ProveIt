# Working in `Analysis/Transseries`

The Lean library is registered as `Transseries` in the repository Lake file.
Add each new module to `Lean/Transseries.lean`. Keep generic transseries modules
free of imports from `FabiusFunction`; put a result that needs a Fabius
definition in the appropriate Fabius bridge module.

Run Lean and Lake builds serially on this host. Build one target at a time,
with its dependencies compiled first; a stale umbrella build can start many
Lean workers and exhaust memory. Check for other `lean` or `lake` processes
before building. The generic modules retain their existing `Fabius` namespace
for source compatibility; new declarations should use `Transseries` unless
they extend that existing API deliberately.

Keep mathematical source in LaTeX and its compiled PDF alongside it. The
two moved volumes currently import the shared Fabius notation file by
relative path. Preserve their provenance and crosswalks when editing them.
