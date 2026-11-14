# Exact obstruction to an unchanged coefficient-three emitter

`lemma.tex` is a self-contained article fragment proving that the numerical
calculus with coefficient three, unchanged restricted implicational head,
unchanged fifth head, generalization and modus ponens derives code one.

The key collision is `E3(1,0)=I3(0,1)=6`. Derived K/S implication rules and
the fixed proof of code zero imply `N3(6)=87`. Generalization gives code
11486, while the fifth-head instance `head5(0,1)` gives its negation,
code 197943987. Modus ponens gives code one.

Run `python3 check.py`. It writes and checks `proof.json` and `result.json`.
The fourteen-line certificate uses primitive rho8, fifth head,
generalization and modus ponens, plus explicitly retained derived K/S rules.
Their coefficient-independent derivations are in the copied upstream
`reference/RestrictedImplication.lean`, with the original license. The
comparison relation is ordinary <=, and both argument-bound hypotheses
hold because `a,b <= pair(a,b) <= 3*pair(a,b)`.

No newly compiled Lean proof or literal-machine halting run is claimed.
The result proves inconsistency of the exact coefficient-three calculus;
a literal machine requires its separate faithful-enumeration/simulation
argument to transfer this refutation to halting.

## Primitive-rule expansion

`python3 expand_basis.py` generates `primitive_proof.json` by expanding the
retained generic source templates and pruning unused ancestors. Then run
`python3 verify_primitive.py` to check the result independently.

The final certificate has 73,393 primitive proof steps: 34,888 rho8 instances,
38,503 modus-ponens steps, one generalization, and one head5 instance. Its
116,171 arithmetic term-DAG nodes have maximum depth 36. The verifier never
parses the Lean source, admits no K/S rule and uses no tautology oracle.
Every rho8 side inequality follows from checked implication-component
containments and the elementary Cantor bounds. Arithmetic expressions are
shared and normalized only by I(0,0)=0; no large numerals are approximated.

Final primitive certificate SHA-256:
`baf316dce45568036fd803382b30ae2669eb504222a39a6be1f3abcad77dcb83`.

The original fourteen-line certificate remains a readable independent
exact-integer check of the short proof skeleton. The primitive certificate
removes K/S from the trusted rule set.
