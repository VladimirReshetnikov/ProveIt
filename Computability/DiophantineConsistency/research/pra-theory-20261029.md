# A candidate first-order PRA presentation

`PRATheory.PRA` is a concrete Foundation `Theory PRALanguage.language`. It
contains full equality axioms for **every** function and relation symbol;
parameterized induction for Foundation's quantifier-free `Semiformula.Open`;
all universal defining equations for zero, projection, composition, and the
base and successor cases of primitive recursion; successor nonzero and
injectivity; and a strict-order definition by explicit primitive-recursive
predecessor, truncated subtraction and nonzero-test codes. Recursion uses the
argument order `(counter, previous value, parameters)` from the function-code
semantics. Its induction formula uses the language's designated `x+1`.

Lean checks each defining equation and basic axiom in the natural-number
structure, proves each induction instance valid there, and concludes
`nat_models_PRA`. Focused checks also exercise equation membership, full
function-symbol congruence, parameterized open-induction membership and all
three basic axioms. The six reports use only `propext`, `Classical.choice`,
and `Quot.sound`. This is a standard-model validation of the exact candidate
theory; it does not identify this presentation with another formal PRA theory,
prove its axiom recognizer primitive recursive, prove conservation, or produce
the requested PRA proof. In particular, the corresponding object-theoretic
successor/add-one bridge and standard-presentation compatibility remain to be
proved.

The final source and focused checks compiled with Lean 4.32 using
`-M6000 -j1 -DElab.async=false` and private outputs at
`/tmp/pra-language-20261029/lib`. The full final main log is empty; the checks
log contains the six reports. All 21 main development snapshots and logs and
both checks attempts are retained in `/tmp/pra-language-20261029/logs`.
Intermediate probes 5, 7, 11, and 15–18 deliberately contained `sorry` to
inspect goals; they are not accepted evidence. The final source contains no
`sorry`, `admit`, or Lean axiom declaration. The first checks attempt failed
on an omitted language parameter; the final one passes. Foundation objects
were linked from the hierarchy author's overlay and Mathlib from the existing
cache; this run does not independently authenticate their full current-source
transitive closure. Independent source review and replay are required.
