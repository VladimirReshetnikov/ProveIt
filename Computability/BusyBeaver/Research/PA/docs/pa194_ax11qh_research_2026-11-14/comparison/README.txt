CURRENT-CORPUS MACHINE COMPARISON

Source snapshot:
VladimirReshetnikov/ProveIt@1c9524d8bf2e0a27b9a16ff622359927f536e663

Read COMPARISON_REPORT.txt for conclusions and evidence boundaries.
principal_designs40.csv/json compares all 40 principal 194-state graph
claims. packet_ledger72.csv/json accounts for all 72 supplied deliveries.
results/frontier_annotated.csv/json distinguishes all 82 spanning 194-state
graphs from two disconnected diagnostics and the 53 experimental 193-state
graphs. Historical status labels are supplied evidence, not new proofs.

Exact independent novelty check (Python 3, standard library only):

  python3 check_novelty.py /path/to/candidate.tm \
      --corpus results/representatives --output fresh_novelty.json

It reparses every candidate-size representative and compares full canonical
tuples, including all spanning roots. The broad test also permits tape
reflection, global bit exchange and discarded halt-edge actions. Those
symmetries are structural; the test does not establish blank-start behavior.
ax11qh_novelty.json is the fresh result for the new PA194AX11QH table.

Rebuild the complete literal/explicit-JSON inventory from a checkout of the
pinned repository (the incoming archives and historical nested ZIPs must
be present at that commit):

  python3 census.py /path/to/ProveIt/Computability/BusyBeaver/Research/PA \
      /path/to/ProveIt/docs/incoming --output /new/output/directory

The scanner records normalized labeled-table hashes, occurrence provenance,
parse failures, and exact graph class representatives. It canonicalizes the
193/194-state frontier, not every size. See its docstring for data formats.
Parameterized source generators, TeX-only tables, .jsonl and other binary
encodings are outside this recognizer. The delivery ledger complements the
literal scan for named proposals.

Files enrich.py, ledger.py, principal_table.py and the readmes/ staging tree
are assembly aids for this research run, not required for the two portable
replays above. They contain acquisition/staging paths and should not be
represented as portable reconstruction tools.

ATTRIBUTION

Machine transition data, historical proof claims and original mechanism
names come from Vladimir Reshetnikov's ProveIt repository and the research
packets identified by each locator. Their James Chang/Andrew James Wade/
ProveIt notices remain applicable to the underlying imported material.
The 76 older mechanism/status annotations were adapted from
pa194_ax11_research_2026-11-14/comparison/frontier194.json and checked against
actual representatives; the six latest principal classes were added from
their README/source descriptions. The scanner and canonical-form comparison
here are separate implementations. Source evidence does not imply a new
end-to-end PA/iPRA formalization.
