# Optional simultaneous singleton elimination

The Python group stage supports `singleton_dag=True`; the whole recognizer
supports `use_group=True, group_singleton_dag=True`. The command-line option
`--group-singleton-dag` enables the group stage automatically. The option is
off by default.

```python
from fastunknot import Diagram
from fastunknot.group_certificate import group_decide

source = Diagram.from_braid(129, list(range(1, 129)))
result = group_decide(source, singleton_dag=True, seconds=None)
assert result["status"] == "UNKNOT"
assert result["certificate"]["version"] == 8
```

## Operation and certificate

If a donor is `U c^epsilon V` with one literal occurrence of either sign of
`c`, it defines `c = (V U)^(-epsilon)`. A batch chooses distinct donor slots
and distinct pivots. Dependencies between chosen pivots must be acyclic.
Arbitrary other letters, repeated parent letters, and mixed signs are allowed.
Every non-donor relator remains in its original slot after substitution.

The producer uses shared raw word circuits. It does not normalize, expand,
or repeatedly traverse already composed inverse images. A batch on `M`
reachable nonempty source nodes has at most `4M` reachable output nodes,
adds at most `5M` nonempty nodes to a persistent arena, and uses polynomial
bit work. These are bounds on the local operation; dictionary behavior,
length metadata, root slots, labels, and earlier unreachable allocations
are accounted for separately in the article.

Version-eight moves contain only an ordered donor/pivot list:

```json
{"kind":"singleton_dag","pivots":[
  {"relation":0,"generator":2},
  {"relation":1,"generator":3}
]}
```

Earlier selected pivots must contain every chosen dependency of a later
pivot. Survivors have rank zero. The independent checker reconstructs
definitions from the intact current relators and checks maximum rank and
capped occurrence counts. The compressed and literal replayers live in
`singleton_dag_verify.py` and do not import producer helpers. The outer
replayer reconstructs the source diagram's complete group presentation.
Older supported certificate versions remain accepted under their existing
interpretations.

## Why dispatch is restricted

The public search applies a batch only when it contains at least two pivots
and removes exactly all but one live generator. It then checks the exponent
of **every** retained relator at rank one. For other candidates, the same
compressed backend continues from its unchanged presentation and move order.
Planning still uses resources, so the option need not preserve every
fixed-budget success or improve every running time.

The general internal operation and checker support partial acyclic batches.
An eager dispatcher caused the Gordian fixture to exhaust 20,000,000 work
after a partial batch of 60 pivots. The terminal guard skips such partial
candidates and later closes that input with a checked three-pivot batch.
The eager source and its complete audit are retained in the dated research
archive.

## Verified scope

The implementation adds 16 test methods to the pinned 992-test suite.
The full run completed 1,008 tests with no failures, errors, or skips.
The independent 81-case source audit (75 distinct PD arrays) contains 243
exact legacy-mode comparisons and 54 positive certificates accepted by both
source replayers. The guarded option gained or lost no positive in that audit.

On closures of `sigma_1 ... sigma_n` on `n+1` strands, the checked group
stage takes one batch instead of a linear number of primitive-forest batches.
The pinned policy incurs quadratic slot-scanning work; the new route has
linear grammar growth and `O(n log(n+1))` charged structural work. At 256
crossings the measured paired median group-stage ratios were 36.47 versus
default and 9.44 versus forest. Earlier diagram simplification was bypassed
for that experiment; these are not complete-recognizer speedups.

The ordinary 19-case whole-recognizer workload showed modest overhead:
paired median default/singleton = 0.954856 and forest/singleton = 0.985518.
Only Gordian used a guarded batch there. Keep the feature opt-in while
improving order selection and eligibility discovery.

The work does not establish general quasi-polynomial unknot recognition.
The associated article supplies full quotient and size proofs, an
NP-completeness result for maximum batch selection on arbitrary positive
presentations, the measured limitations, and ten further research topics.
