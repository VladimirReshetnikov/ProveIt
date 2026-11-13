# Serialized-import audit for the 92-operation proof objects

The observed selected-project import closures of `QCube92`, `QCube92Model`,
`FreeJRootBinding`, and `QCube92Existence` do **not** include the conflicting
`FreeJOrdinaryTailWitness` module. The closures contain respectively 29, 30,
31, and 38 selected-project names, counting the root itself. Every project
ancestor other than the four newly built proof objects has the same object
hash under its producer's recorded search path as in both the previously
recorded header inventory and the 94-model union. The three new proof objects
used as dependencies are also checked against their producer hashes. This is
relevant to the proposed combined halt-model build;
it does not by itself establish that build's correctness.

The two tail objects really do differ. The original 92-author search path
contains object `b36cc3c0…`, whose serialized header imports
`FreeJSignedTransport`. The 94-model union contains `3af9bb5c…`, whose header
imports `DiophantineConsistency.FreeJSignedTransport`. The adjacent retained
`.lean` files differ only in that import line. That source comparison does not
prove either object was compiled from its adjacent source. For both objects,
the inspected `.olean.private`, `.olean.server`, `.ilean`, `.ir`, and hash
companion paths were absent; the `.lean` files were present. The machine
result records the inspected link and resolved companion paths for all
selected shared ancestors as well. These are point-in-time filesystem
observations, not a general statement about Lean's dynamic loading behavior.

`scan.py` performed one guarded Lean `readModuleData` header-reader invocation
on the four produced objects and both conflicting tail objects. It checked the
four producer receipts, source and object hashes, and the old serialized
header inventory and 94-model manifest. For each root it traversed the stored
import graph starting from the newly read headers. For each visited project
module it resolved the first existing object using **that producer's own
recorded `LEAN_PATH` order**. Existing-project ancestors were rehashed against
the object whose header was recorded and compared with the corresponding
selected object in the 94-model union; the new proof objects were checked
against their producer hashes. The result includes complete per-root selected and outside
lists, paths, hashes, and companion observations. The 94 tail header also
matches its earlier stored header. The previously recorded inventory was not
fully reread by this scan.

The reader exited zero in approximately 0.38 seconds. Its pre-launch sample
saw 18,692,704 KiB available and no Lean process; the post-launch sample saw
18,701,528 KiB and no Lean process. Launch required at least 8 GiB available
and fewer than two pre-existing Lean processes; the reader had a 3-GiB Lean
limit and a 60-second timeout. These samples do not rule out an overlap or a
memory dip between observations.

The captured machine-readable result is
`observations/attempt01/result.json`, SHA-256
`af847f4a3903770fd50bf7b7f09d597f748fa83ab0c3f4c0b7ae79dff192a615`.
`audit.py` independently reparses the captured headers, traverses the graph,
checks the first-resolved paths, hashes and recorded companions, and confirms
the single-line retained source difference. Run it read-only with
`python3 -I -S -B audit.py`; its successful captured output is
`observations/audit01.stdout`. Both scripts require the recorded temporary
provider paths. The scan refuses to overwrite an existing observation.

The graph has 20 outside names at the existence root in Foundation, Mathlib,
Lean or Init. Their transitive imports were not scanned. Dynamic loading,
complete project and package ancestry, and historical source-to-object
provenance remain inherited. Consequently this is not an assertion that an
arbitrary mixed-provider environment is safe, a fresh end-to-end kernel replay,
or an internal iPRA proof.
