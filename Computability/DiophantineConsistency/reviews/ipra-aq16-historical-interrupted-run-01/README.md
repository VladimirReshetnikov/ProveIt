# Interrupted AQ16 historical pair, run 01

The outer launch session `36391` actually exited **143** after reporting
successful freezing and preparation, with no final coordinator output. The
cause of termination is unknown. At the subsequent recorded UTC observation,
the coordinator state was `RUNNING`, the author state was `PASS` with 52
records, the peer state was `RUNNING` with 31 records, and the coordinator
observation file was absent. A targeted process snapshot found no remaining
matching Python or Lean process. These observations do not establish a paired
result or identify who or what caused the termination.

The complete observed outer output, point-in-time states, both process logs,
available sibling logs and per-file hashes are preserved here. The original
run remains unchanged at `/tmp/ipra-aq16-historical-paired-run-01`. Do not
reuse its partially built peer artifacts. Any retry requires a fresh output
root, a new protected preparation window, actual exit capture, and a separate
post-result artifact audit.
