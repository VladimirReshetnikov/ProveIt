# Exact Rotation240 blank initialization

The exact 240-state table reaches the recorded whole-tape checkpoint after **409,691 transitions** from the blank initial configuration. `BootRotation240Chunk009.bootstrap409691` proves `ZipRep (machineRotation240.run 409691) checkpoint409691`; `bootstrap_active_through` proves that the run remains active at every earlier time, including that endpoint. The ten checked modules contain 34 contiguous power-of-two blocks. Their actual source and audit runs passed with **72 axiom probes, 102 typed callers and zero warnings**.

| Unit | Initial step | Final step | Block depths |
|---|---:|---:|---|
| First | 0 | 1,024 | 10 |
| Chunk001 | 1,024 | 17,408 | 14 |
| Chunk002 | 17,408 | 82,944 | 14, 14, 14, 14 |
| Chunk003 | 82,944 | 148,480 | 14, 14, 14, 14 |
| Chunk004 | 148,480 | 214,016 | 14, 14, 14, 14 |
| Chunk005 | 214,016 | 279,552 | 14, 14, 14, 14 |
| Chunk006 | 279,552 | 345,088 | 14, 14, 14, 14 |
| Chunk007 | 345,088 | 402,432 | 14, 14, 14, 13 |
| Chunk008 | 402,432 | 409,664 | 12, 11, 10, 6 |
| Chunk009 | 409,664 | 409,691 | 4, 3, 1, 0 |

The endpoint has canonical state 84 and head −5. Its finite zipper has left list `true :: replicate 9 false` and a 707-bit right list; its complete support contains 351 one-cells. `ZipRep` identifies the state, head and every tape position, with zeros outside the represented finite lists. The generated checkpoint data were discharged by `decide +kernel` and the checked `FiniteZipper.zipBlock_sound` theorem. The endpoint's identification with the runtime's initial frame is a separate theorem; this packet does not establish decoder coverage, a full binary consistency equivalence or an internal PA endpoint.

Each unit used a fresh source/audit pair, one Lean thread, 4,096 MiB and a shared 120-second deadline, with default proof limits. Total source time was 246.429 seconds and total audit time 4.994 seconds; the largest source run took 40.188 seconds. All reports use only `propext` and `Quot.sound`. Guards recorded the fresh object and its first import resolution before the audit, then checked input and object hashes again. No dependency build, download or version query was performed by these runs. Existing dependency-object provenance and its historical limitations remain explicit in the raw records.

The [final actual record](results/rotation240-bootstrap-verification.json), [publication inventory](results/rotation240-bootstrap-publication.json), and [independent existing-evidence review](rotation240-bootstrap/review/actual-review.json) identify the selected bytes. The final [Lean source](../../Lean/BusyBeaver/ZFC/BootRotation240Chunk009.lean) imports the preceding nine modules; [its audit](rotation240-bootstrap/chunk009/Audit.lean) includes an arbitrary tape-position client. The preserved [history archive](rotation240-bootstrap/history.json.gz) contains the exact source-generation proposals, guard templates and bindings, preparations, source/audit snapshots, actual logs, serial driver and available reviews. All ten selected proof attempts are first-run successes; no failed proof is invented. Earlier unexecuted drafts and historical limitations are retained verbatim.

The original guards in `rotation240-bootstrap/<unit>/check.py` retain their recorded scratch paths and prerequisite cache identities. Publication changes no guard or proof bytes and executes no proof. Replaying these guards requires their recorded historical inputs; the maintained Lean modules can instead be rebuilt in dependency order with matching foundational modules. The history archive is a UTF-8 JSON object whose `files` entries give each original path, SHA-256 and exact text; compiled objects and cache links are excluded. The finite zipper definitions and whole-tape soundness route retain the underlying Mira-Cult, Jeff Ketchersid, Andrew James Wade and ProveIt attribution recorded in their source provenance.
