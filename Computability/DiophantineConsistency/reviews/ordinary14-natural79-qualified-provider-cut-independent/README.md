# Independent review: natural-79 qualified-provider cut

The [natural-79 provider-cut packet](../../research/ordinary14-natural79-qualified-provider-cut/README.md)
accurately describes the bounded, point-in-time source and object observations
reproduced here. This is not Lean dependency resolution, a provider-compatibility
certificate, a build authorization, or an iPRA theorem.

The independent checker pins the overlay inventory, its 195 inert source
snapshots, the prior natural-80 cut and the selected P72/base metadata. It
reparses every snapshot's simple initial imports, then independently performs
a breadth-first walk from the 44 direct qualified names. The resulting 44
missing selected-P72 project objects with current source candidates, 46
selected P72 project frontier objects and five guarded-package Mathlib objects
match the original receipt. For each project source and object it rechecks the
recorded path and hash observations; the 39 additional source candidates,
six additional frontier names and one additional external name relative to
the prior cut match the source packet. These are observations of current
records and files, not independent historical producer authentication.

The checker independently repeats the 239-name, eight-root, 13-suffix scan
and obtains the same six `.olean` hits, belonging to three qualified module
names in the captured endpoint and failed Carrier65 roots. Those are
nonselected alternate paths. Matching or differing object hashes do not
establish provider compatibility, and the bounded scan does not cover a future
output root or other paths and suffixes.

The scanner handles only the observed simple source headers and stops at
selected objects. It does not follow compiled imports or the external source
closure, establish Lean's namespace/search behavior, inspect every companion,
verify source-to-object provenance, trace runtime loads or reserve an exclusive
build slot. Filesystem reads are non-atomic and the retained roots may change.
The old BFS943 branch, current symbolic endpoint, axiom reports, and physical
coefficient/PDF binding remain unverified by this audit.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary14-natural79-qualified-provider-cut-independent/check.py | cmp - reviews/ordinary14-natural79-qualified-provider-cut-independent/result.json
```
