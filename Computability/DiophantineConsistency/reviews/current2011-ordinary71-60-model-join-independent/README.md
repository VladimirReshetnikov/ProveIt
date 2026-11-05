# Independent review: 71/60 and 67/94 all-model zero join

The read-only [checker](check.py) exited 0 and produced [result.json](result.json).
The source theorem `sameZero94` states that, for each valuation `v` in each
model satisfying the stated IΣ₁ assumptions, the positive-shifted literal
71/60 expression vanishes iff the positive-shifted 67/94 expression does so
at **that same valuation**. It instantiates the generic ordered-ring theorem
using the checked model facts, fixed beta positivity, and positivity of each
shifted coordinate; Lean's definitional `change` identifies the two generic
value definitions.

The audit checks the source and exact statement, successful child and actual
outer session 63341, the named axiom report, output object and all 393
recorded direct/nested guard slots. The pinned generic and literal predecessor
objects are selected directly. It also reruns the independent generic theorem,
literal-row/evaluator, and graph/degree reviews with matching outputs.

The join does not itself state an iPRA theorem or formally interpret the JSON
and coefficient files in Lean. The graph and exact degree checks are separate;
the captured provider's package-transitive and dynamic ancestry remains
inherited, and this audit does not replay Lean or rebuild that provider.

Reproduce from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/current2011-ordinary71-60-model-join-independent/check.py
```
