# Triage of the 141 direct project inputs

The read-only `check.py` inventories the 141 project modules just outside
the captured 186-module impact cone. It pins the final selected closure, the
186-cone inventory, six selected producer-run results and the earlier BFS
serialized capture. It rehashes the current selected `.olean` and companion
files and records each captured header; it invokes no Lean.

At the recorded selection:

* **16 of 141** have an exact selected output match in one of the six pinned
  runs: the `.olean` realpath and all recorded companion hashes match, and
  that stage's recorded exit is zero. This check does not establish the
  stage's entire upstream producer history.
* The earlier BFS serialized capture contains **126** entries with all
  recorded companion hashes equal to the final selection, **one** with a
  difference, and **14** absent. The different name is the already-rebuilt
  `DiophantineConsistency.ArithmeticNegativeNorms`.
* The earlier capture names candidate producer receipts for **41** inputs;
  all 41 receipt files currently match their captured hashes. A candidate
  receipt is evidence to investigate, not by itself identification of the
  exact current producer or proof of its producer-time direct imports.

The counts overlap: among the 125 inputs without an exact selected producer
in the six runs, 115 match all companions in the earlier capture; the same
captured `.olean` realpaths are recorded for those 115, and 30 have candidate
receipts. The remaining 10 are absent from that same-hash subset. Full
per-module records and the distinction between realpath, object hashes,
captured direct comparisons and candidate receipts are in attempt01 stdout.

Author attempt01 exited 0. Checker SHA-256 is
`0226c4646a85e4bc22f75ce1673960617fa7e3a1ee86e939e4266c98f54a5082`,
terminal SHA-256 is
`94a001c50e462013f7576d3b2e3fe909aa6c62a882ebf3627dc9b569643d81a4`,
and stdout SHA-256 is
`87c27b168b3d242214d75e8de5c4165dd2c7ac9005ac680c6bc812558dbd8575`.
The [independent triage audit](../../reviews/trace75-upstream-141-inventory-independent/README.md)
rechecked the classifications and receipt hashes without establishing the
remaining producer-time or transitive ancestry.

The next work is to authenticate producer source, logs and producer-time
direct selections per candidate where such records exist, and investigate
the remaining unidentified records. A source-current replay must also assess
upstream dependencies and any changed or dynamically loaded imports; this
triage and the earlier 186-node order do not establish a complete current
source closure, package ancestry or independent Lean replay.
