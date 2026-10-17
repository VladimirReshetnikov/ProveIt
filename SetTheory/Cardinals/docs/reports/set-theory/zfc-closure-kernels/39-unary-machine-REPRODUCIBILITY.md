# Replaying the machine material

From the archive root, run:

```sh
python3 verify.py
python3 verify.py --search
```

The first command reruns the support diagnostics, theory specification checks,
and both literal machine/table/bootstrap audits. It compares every field of
their parsed JSON outputs with the retained results. The optional search run
compiles the two C++17 programs and replays their four radius-4/radius-6 searches
on the retained contexts. It compares every parsed state, incoming edge,
replacement option, and summary counter against the retained logs, and checks
the summaries against `search_summary.json`.

Python 3.10 or later and its standard library suffice for the default checks.
The optional searches also require a C++17 compiler, selected by `CXX` or
`--compiler`. No network connection is used. All programs run in a temporary
copy; their outputs, bytecode caches, and compiled executables are excluded
from the extracted archive. The root Makefile provides `verify` and
`verify-search` targets for the same commands.

The optional search replay uses the retained context inventories. To regenerate
the context inventories themselves, copy this entire directory to a working
directory and follow the longer commands in `MACHINE_AUDIT.md`. Context JSON
contains an elapsed-time field, which naturally changes when regenerated.
Those context-generation scripts reuse the attributed affine executor and its
register-box summaries; their results are diagnostic, not proof certificates.

The portable audit entry points are the new scripts at this directory's top
level. They resolve data paths relative to their own file location and pass the
baseline table explicitly to the retained public 253 generator. The selected
files under `upstream/` and `upstream253/` preserve their original locations
within their respective snapshots. Their standalone upstream defaults assume
a complete upstream repository, which is not included here. In particular,
this archive is not a Coq build tree. Upstream source and attribution details
are recorded in `MACHINE_AUDIT.md` and `provenance.json`.

No executable binaries or generated verification copies are part of this
directory. Passing these checks reproduces the stated finite evidence; it
does not prove a new state count or internalize the Coq theorem in ZFC.
