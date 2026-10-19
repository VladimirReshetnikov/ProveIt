# Checked ranks and bounds on internal formula codes

The unchanged [`CodedRank`](Lean/BoundedZFCConsistency/CodedRank.lean) now
passes a [local Lean check](results/coded-rank-verification.json). Under its
explicit semantic axiom bundle, every internal formula code has unique sigma
and pi ranks. The ranks agree with the external definitions on quotations.
Bounds descend to subformulas and are preserved by renaming; consequently,
bounding every recorded judgement and context also bounds every formula
parameter of all seventeen inference rules.

The module's `logicConForm` concerns bounded derivations from the empty
context: it is a pure-logic consistency sentence. Some older docstrings call
it `Con_n(ZFC)`, but its definition does not recognize ZFC axioms. The actual
ZFC axiom predicate and reflection argument are later work. The semantic
consequence/completeness theorem here retains its explicit hypothesis.

The check passes sixteen named axiom probes and sixteen typed callers, with
zero warnings and only standard Lean axioms. Source and audit took 4.735 and
0.292 seconds under one thread, 4,096 MiB and a shared 120-second deadline.
The source's existing recursion limit of 8,000 is retained; the audit uses
default proof limits. Sixteen exact project source/object pairs and Init are
selected from the actual coded-derivation and completeness checks plus the
previously accepted Choice pair. The unrelated prerequisites of that older
Choice provider record are outside this check's scope.

The initial source compilation passed, but its audit exceeded the default
recursion limit by unfolding the large sentence closure. Adding the source's
existing local irreducibility attribute for `SetTheory.sealF` to the audit
resolved the failure. No statement or proof limit changed. The
[publication](results/coded-rank-publication.json) and
[history](coded-rank/history.json.gz) preserve both attempts, exact bindings,
raw logs and the audit-only correction.
