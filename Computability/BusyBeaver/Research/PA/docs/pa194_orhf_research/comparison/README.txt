PORTABLE COMPARISON AND NOVELTY EVIDENCE
=======================================

Pinned upstream:
https://github.com/VladimirReshetnikov/ProveIt/tree/883da8d55452ea097910ed2509a1eefc833ce292

The comparison contains 104 distinct named claimed 194-state designs from
100 filed PA packets and the six incoming archives. It independently recounts
all 104, preserves aliases, and gives an explanatory 38-family grouping. These
are proposals with attributed proof status; the roster is not an independent
certification of all 104 absolute consistency calibrations.

The retained corpus contains:
  corpus194/: 548 complete graph-spanning 194-state action classes, plus two
             disconnected nonminimal diagnostic byte forms;
  corpus193/:all 55 complete graph-spanning 193-state catalog classes.

coverage.json verifies all 528 filed catalogued 194 classes and all 55 catalogued 193
classes, with zero omissions. The 20 additional spanning 194 classes consist of
13 named incoming proposals and seven intermediate/diagnostic tables. All104
named classes are represented. Thus a missing local duplicate file does not
remove a class from the comparison. State graph reachability is an abstract
transition-table property, not proof that every state occurs on the blank run.

Scope: complete numeric five-column binary L/R tables in the delivered machine
corpus and recursively inspected incoming ZIPs, supplemented by the pinned
repository catalog. No arbitrary generator is executed to enumerate an infinite
family, and no table is guessed from prose. The source locators and hashes of
all retained representatives are in corpus_index.json and class_catalog.csv.

FINAL NOVELTY RESULT
Both PA194ORHF and PA194ORHBF are absent from all 548 prior spanning 194 graphs
and the two diagnostic tables, and differ from each other, even allowing
arbitrary state names and root changes, reflection, global bit exchange, and
erased write/move decorations on halt entry. Bit exchange strengthens the
graph-identity test; it is not asserted to preserve a zero-blank computation.

The independent checker obtains a stable singleton action-bisimulation
partition for each candidate. A nonminimal table cannot be isomorphic to it.
For minimal tables the resulting canonical labels determine the entire graph,
so exact canonical BYTE equality decides the allowed isomorphism. No conclusion
rests on hashing alone. Renaming and erased-halt-action positive controls pass.

REPLAY FROM THE RESEARCH PACKAGE ROOT
Python 3.10+ and the standard library suffice; no network or proof assistant.
Do not disable assertions with -O.

  python3 -B comparison/check_coverage.py --out /tmp/pa194-coverage.json

  python3 -B comparison/fast_novelty.py --corpus comparison/corpus194 \
    --candidate machines/PA194ORHF/machine.tm \
    --candidate machines/PA194ORHBF/machine.tm \
    --out /tmp/pa194-novelty.json

  python3 -B comparison/screen193.py --out /tmp/pa194-screen193.json

The full 193-state audit tries all 10,615 state/start choices. Its observed 112
finite halts, 10,499 certified outward rays, and four 100,000-step caps are in
screen193.json. Caps remain unresolved by that bounded run. The source-level
reasons rejecting the two capped graph classes are documented separately.
None of this is a general 194-state lower bound.

The complete 104-name mapping is named_designs104.csv. comparison_notes.txt
explains the mechanism axes, alias pitfalls, proof boundary and 193-state audit.
The optional census.py can inventory a full local checkout independently; the
reported final novelty uses only the small packaged corpora.
