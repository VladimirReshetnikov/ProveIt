DEFERRED RETAINED-MAJOR CONSTRUCTION
==================================

This folder contains a two-token simplification of the incoming shared_leaf
stream checker, its exact source control, a separately charged whole-JSON
framing of each, inherited fixtures, a source-correspondence proof and tests.

Read proof.txt for the precise scope and limits. The arithmetic theory and its
bi-interpretation are inherited unchanged. This is not a new mathematical
axiomatization or a theorem of minimality, and one program does not attain all
reported coordinate minima.

Run:
  python3 verify.py
  python3 code/checker240.py < fixtures/lines/global_guarded_induction_with_used_hypothesis.jsonl
  python3 code/checker245_whole.py < fixtures/whole/global_guarded_induction_with_used_hypothesis.json

Every measured module is standalone and uses only Python's standard library.
The parser and the required ACCEPT line are included in its metrics.

The whole-JSON form stores the goal last and consumes the array backwards.
The line form stores the goal first and consumes later lines forwards.
Neither form validates every part of the inherited canonical input promise.
See PROVENANCE.json and proof.txt for attribution and exact source contracts.
