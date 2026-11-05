# Independent review: 70/84 and 67/94 all-model zero join

The read-only [checker](check.py) exited 0 and produced [result.json](result.json).
The checked source theorem states that, for each valuation in each model
satisfying the stated IΣ₁ assumptions, the positive-shifted literal 70/84
expression vanishes iff the positive-shifted 67/94 expression vanishes at
**the same valuation**. It instantiates the generic ordered-ring theorem
using the model facts, fixed-beta positivity and shifted-coordinate positivity.

The audit rechecked the exact source statement, child and actual outer session
56964, the named axiom report, output object, and all 528 recorded
direct/nested guard slots. It verified the selected generic and literal objects
and reran their independent reviews and the external graph/degree audit.

The join does not itself assert an iPRA derivation, a Lean degree theorem or
Lean JSON/file semantics. Historical package-transitive, dynamic and
between-observation ancestry remains inherited; no Lean replay or new base
rebuild was performed during this audit.

Reproduce from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/current2011-ordinary70-84-model-join-independent/check.py
```
