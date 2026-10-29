# Addition by one and successor exhaustion in the candidate theory

`PRAAddOne.PRA_proves_addOne` is an actual Foundation proof-existence
statement `PRA ⊢ addOneSentence`, where the sentence universally asserts that
the designated addition applied to one equals the primitive successor. The
argument derives this identity from the actual composition, projection and
primitive-recursion axioms in every equality model of `PRA`, then applies
Foundation completeness. It does not infer provability from standard-Nat truth.

`PRAExhaustion.PRA_proves_exhaustion` similarly proves in the candidate theory
that every element is zero or is the successor of its coded predecessor. In
every equality model, the predecessor recursion step proves
`pred(succ(x)) = x`; the proof then uses the actual parameterized open induction
axiom, with the addition-by-one identity, and applies completeness. The exact
induction body is checked syntactically open.

Both main modules and their checks compile under Lean 4.32 with
`-M6000 -j1 -DElab.async=false` into `/tmp/pra-language-20261029/lib`. Their
focused reports use only `propext`, `Classical.choice` and `Quot.sound`. The
Foundation overlay and existing Mathlib cache are inherited boundaries; the
current-source closure and independent replay are separate checks. Development
snapshots and diagnostics are retained under the adjacent `logs`: the add-one
main has 18 attempts (9–11 were admitted trace probes), while exhaustion has
19 attempts (1 and 9–10 were admitted probes). The final accepted sources have
no admitted proofs. The already-reviewed add-one source was restored to its
exact earlier bytes before the exhaustion pair was built.

These are theorems of the explicitly defined candidate object theory. They do
not yet identify it with a standard PRA presentation or establish conservation
of IΣ₁; neither proves the Diophantine consistency equivalence in PRA.
