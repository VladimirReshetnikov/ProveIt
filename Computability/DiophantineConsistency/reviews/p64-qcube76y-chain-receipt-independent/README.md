# Independent 76Y proof-chain receipt audit

A read-only audit of the frozen 76Y chain returned **PASS** for eleven
recorded successful checks: generated graph, generic bounds, ring binding,
graph-model split/main root, actual-size bound, new and old witness guards,
conditional witness maps, conditional and full model joins, and the iPRA
endpoint client. No Lean process was run during this audit.

The [checker](check.py) rehashes each retained receipt and full log, the
currently selected source and output object, and every recorded direct guard
and absence. It checks exit 0, no recorded monitor stop, at least one RSS
sample, and the reported sampled peaks against the recorded limits. It
requires the full axiom report text to match exactly: the ring-only bindings
and two strict-guard evaluator lemmas report `[propext]`; the model and
endpoint statements report `[propext, Classical.choice, Quot.sound]`, with
no `sorryAx` or warning text. It resolves each syntactic direct import using
the recorded `LEAN_PATH`, verifies the selected object has a direct guard,
and connects each intra-chain import to the exact hash of the preceding
successful object. It also checks the 77 endpoint receipt and matches that
object to the 76Y endpoint's direct parent.

The reviewed full join states positive-zero equivalence of the 76Y and 77
Lean graphs for every natural port tuple in each indicated IΣ₁ model. The
client composes that with the 77 bridge and states native, standard and
equality-only iPRA derivability for the positive-shifted 76Y expression at
the symbolic compact44 tuple and the selected mapped refutation negation.
These are proof-existence claims, not assertions that ZFC is consistent.

The first iPRA client attempt is separately checked as **FAILED**, with exit
`−6`, a Lean interpreter memory exception, and no object. Its subsequent
retry is the recorded endpoint PASS. The eleven passing runners' `group_rss`
functions have identical parsed function bodies, and their missing-child
helper hashes match. Their 250 ms RSS and available-memory observations are
sampling, not hard limits or independently reconstructed process histories.
The successful endpoint retry runner compares against a **180-second** timeout
but labels that stop reason “120-second timeout”; no timeout occurred, so this
diagnostic-only discrepancy does not change the recorded PASS.

This audit checks direct dependencies and present bytes, not a fresh Lean
replay or full transitive project, package, dynamic-library, or search-path
ancestry. Current import resolution does not by itself authenticate every earlier
search-path absence at the time of each run. The symbolic graph/port
correspondence with external coefficients, JSON, gzip, TeX and PDF remains
outside scope. The audit depends on the
machine-specific temporary provider objects still being present; rerunning it
later can fail if they are removed or changed. The comprehensive machine
results and direct import lists are in [`result.json`](result.json).

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube76y-chain-receipt-independent/check.py
```

| Artifact | SHA-256 |
| --- | --- |
| `check.py` | `8778967b23808db26b810e0648bb6e7c7c55a8c5d0b1168f324a6c3f7377cce3` |
| `result.json` | `5dc948ce7d34a5dc8388f8e279f211b04f1572cce07ddf89631e185f4e636a6d` |
