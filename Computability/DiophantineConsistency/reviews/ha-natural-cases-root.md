# HA zero or successor: independent root review

26 October2026. Root read the entire new main/check pair and author receipt.
The theorem is an actual HA proof of `t=0 ∨ ∃z t=S z`, including arbitrary
terms with free parameters. Its formula induction uses equality reflexivity
at zero and the current induction variable as the successor witness. The
induction hypothesis is legitimately unused. The existential binder shifts
all ambient term variables; the focused checks cover this capture boundary.
The small relative disjunction/existential introduction helpers retain their
actual finite axiom lists.

Root independently compiled both leaves with `-M6000 -j1
-DElab.async=false`. Both passed, with an empty main log and11 reports
containing only `propext`, `Quot.sound`, or no axioms. Both objects match
the author byte for byte. Eight cached custom prerequisites were reused;
53 input/source/cache-source/object observations, including repeated
observations in the author input list, were rechecked before and after.
There was no fresh prerequisite or package-closure build.

Root also rehashed all12 files of the durable author bundle, including its
preserved failed focused-check draft. Exact commands, logs, source/object
hashes and cached boundaries are in
[ha-natural-cases-root-replay/ROOT.json](ha-natural-cases-root-replay/ROOT.json).
This arithmetic decomposition does not assert general excluded middle or
complete the requested HA consistency equivalence.
