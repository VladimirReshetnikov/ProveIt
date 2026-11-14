PINNED COMPARISON ARTIFACTS
===========================

Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 1e407ae841e4666f932777fad977ba784ebbcfd5

Scope
-----
The narrative ledger covers all 41 filed research-packet directories in
Computability/BusyBeaver/Research/PA/docs and all five archives currently
in docs/incoming at this exact commit. Proof-layer pa194-* directories
are not counted as independent research packets.

The fresh literal-table census scans the entire PA subtree plus all
incoming ZIPs and recursively referenced ZIP payloads. Archive payloads
are de-duplicated by bytes. It recognizes complete numeric binary
five-column .tm/.txt/.tsv/.csv tables with one undefined halting target.
JSON-encoded tables, emitter sources and narrative-only proposals are
not claimed to be literal tables; they are considered in the narrative
ledger where relevant.

Results
-------
17,551 direct PA files inspected; 19 distinct ZIP payloads and 31 archive
references; 3,741 literal table occurrences, 666 byte identities,
476 action-graph classes and two disconnected small synthetic tables
not classified by the spanning-root method. No parser errors occurred.

The 194-state frontier has 261 occurrences, 51 byte identities and
28 action-graph classes. Those comprise 16 reported principal/companion
results, six supplementary results, three search seeds and three rejected
candidates. The status labels describe evidence in the packets, not a
new independent replay of every historical proof.

The five packets named PA194C/pa194c share one exact dense table.
PA194X in the R packet and PA194CSZ in the Q/radix packets are also the
same exact dense table. Repeated packets must not be counted as distinct
machine designs.

Files
-----
packet_ledger.csv/json/tex:
  All 46 packets, their specific contribution, original paths and hashes.
  The TeX fragment requires longtable and booktabs.

frontier194.csv/json:
  Every one of the 28 recognized 194-state graph classes, with principal
  table hashes, provenance paths, evidence status, state/interface counts
  and specific design changes.

census/census.json:
  Exact machine inventory, occurrence paths, archive identities and graph
  classes. Paths containing ! denote ZIP member provenance.

census/tables/<sha256>.tm:
  All 666 recognized table byte identities, retained unchanged.

census.py:
  Reproduce the scan from the pinned repository checkout:
    python3 census.py --repo /path/to/ProveIt --output /tmp/fresh-census

check_novelty.py:
  Exact tuple comparison for a candidate against all same-state-count
  prior tables, allowing arbitrary state relabeling and start choice,
  tape reflection, symbol exchange and their combination:
    python3 check_novelty.py /path/to/machine.tm \
      --census census/census.json --output /tmp/novelty.json

ncs_novelty.json:
  PA194NS result (NCS was its internal working name), exact candidate SHA:
  19935635f2c5722f5a72977d20a7019764a28573e12d1d0bce398245576c33b1.
  No match among all 51 prior 194-state byte forms / 28 action graphs.
  All 194 possible roots span the candidate; 776 transformed roots are
  examined. Equality decisions compare full canonical tuples, not only
  cryptographic digests.

calibration_audit.txt:
  Independent review of inherited arithmetic calibration, the PA194NS
  command compiler, scheduler coding and exact tape-transfer obligations.

Reproduction and limitations
----------------------------
Python 3 standard library and rg are sufficient. The repository version
must match the pinned commit to reproduce these census counts. Supplied
copies of the table bytes permit the novelty comparison without network
access or the complete checkout.

Graph classes are not logical equivalence classes. Passing a graph check,
command-level proof or bounded simulation alone does not establish a
consistency-calibrated blank-input machine. No finite corpus or failed
search proves that fewer than 194 states is impossible.
