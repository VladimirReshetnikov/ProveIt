# Distributed separation: exact mathematical interface

This candidate retains PA196's numerical coding: `I(a,b)=4 pair(a,b)`,
`M(a,b)=4 pair(a,b)+1`, `U(a,B)=4 pair(B,a)+2`, and
`E(a,b)=4 pair(a,b)+3`. Falsity is code 1, and every use of classical
reasoning below is in the retained numeric calculus after its established
propositional bootstrap. The existing truth, generalization, restricted
propositional head, six logical heads, and gate guards are preserved.

For the gate, write `a=H`, `b=D`, `c=A`, exactly as in PA196. Put

* `Delta = E(a,b) -> U(c,E(a,b))`;
* `V = M(a,b) -> U(c,M(a,b))`;
* `P = c -> M(c,b)`;
* `L = M(a,b) -> P`;
* `R = M(c,b) -> c`;
* `S1 = U(b,L)` and `S2 = U(b,R)`.

The old gate uses `S=U(b,L AND R)` and
`Q=U(c,S -> NOT P)`. The new gate uses
`Q'=U(c,S1 -> (S2 -> NOT P))`. It leaves
`F'=NOT(Delta -> (V -> Q'))` in the accumulator when the existing guard
`c != a,b` holds, and leaves code 0 when that guard fails.

The retained distribution head and generalization prove
`U(b,L AND R) <-> (U(b,L) AND U(b,R))`. Classical currying then proves
`(S -> NOT P) <-> (S1 -> (S2 -> NOT P))`; generalization and the
distribution head lift this equivalence under `U(c,...)`. Propositional
congruence gives `F <-> F'`. No new variable-freshness assumption enters
this transformation. It applies to every numerical selector, including
collisions between `a` and `b`; the `c != a,b` guard is unchanged.

The exact selected word also changes the order of the six pushed heads
from `[1,2,3,4,5,6]` in the PA196 paper to `[1,6,2,3,4,5]`. In head 6,
the antecedents are exchanged, producing

`U(D,A -> H) -> (U(D,A) -> U(D,H))`.

This is equivalent to the old head by the same retained propositional
calculus. The other five heads and the preceding saved accumulator,
generalization, and restricted propositional head are byte-for-byte the
same macro words. Permuting available head pushes and replacing formulas
by uniformly interderivable formulas preserves the set of derivable
formula codes; an updated compiler must select the corresponding stack
position. The register driver still pushes nine items in all. The exact
word generator and proof of the 199-token count accompany this note.

The resulting word has one extra `node55` (copy D), one fewer `node65`
(form the constructor base), and two fewer `node49` (push/zero) calls.
Their respective primitive lengths are 26, 27, and 19, so the complete
source has `3812 + 26 - 27 - 2*19 = 3773` primitive occurrences. All
other macro multiplicities agree. Every ordinary macro is closed in the
binary source-language control sense; the single final `breakTo 1`
remains last, so reassociating the macro sequence preserves its ordinal
primitive control graph after relocation.

`inputs/grammar67.json` is a finite dictionary-grammar witness found by
a time-limited MILP search. Every selected production is checked by
`verify_grammar.py` without the solver. The sum of `(arity - 1)` over
the selected productions is exactly 67. This proves the existence of a
binary grammar with at most 67 internal rules before routing constraints.
It does **not** prove that 67 is minimal, or that a 195-state physical
Turing machine exists. A suitable association must still satisfy the
tape-routing bounds, and all physical folds and arbitrary-register frame
contracts require separate checks.

This is a source simplification and a proof-interface description, not
a completed PA formalization. It does not close the separately documented
gap between external soundness and a PA proof of the full consistency
biconditional for the published PA196 baseline.

## Additional exact reuse witnesses

The existing PA196 source node 60 is the pair `(inc 1, inc 1)`. Its physical
reader is native state 99, whose rows are `0 R 61` and `1 R 61`; native 61 is
the existing increment dispatcher. A grammar subtree with precisely this
association can therefore refer to this existing reader. The portable
checker binds this fact to both the pinned source and the pinned literal
table via the upstream conjugacy map.

`grammar_freeii66.json` is a second grammar for the exact selected 199-token
word. Its integer binary-rule upper bound is 67, of which one is this
already-present reader, leaving an upper bound of 66 **new** AX readers
before routing constraints and context folds. `baseline_freeii67.json`
similarly has 68 binary rules, one reused reader, and 67 new readers for the
unchanged 201-token PA196 word. The MILP solves were time limited and do not
establish minimality. Both witnesses and all their expansions are checked
without the solver by `verify_grammar.py`.

These are representation-cost upper bounds, not physical machines with
corresponding state counts. A feasible tape layout must also honor incoming
contexts of shared macro entries and the transient extra zero introduced
by increment return handling, in addition to static source-path bounds.
Subsequent physical compilation and arbitrary-frame verification decide
whether these grammars can realize the anticipated savings.
