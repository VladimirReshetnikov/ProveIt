# Reuse one later rho8 lemma

This plan reorders and reuses Source 149’s finite derivation of unrestricted `rho8` from dominated `rho8`. The retained proof has **629 theorem nodes and 735 compact interpreter instructions**, compared with the previous 674 / 780. Both the direct Lean proof and the compact Rocq proof have passed their exact-target kernel checks. This is a proof reduction, not a claim that the derivation is minimal or that the repository as a whole becomes smaller.

The useful additional lemma is original node **1013**,

```text
A → ((A → B) → B).
```

Its proof can be placed before five earlier-numbered instances (original nodes 179, 297, 427, 612 and 769). Reusing that lemma removes repeated dependencies. The original numbering was a production order, so it need not constrain a new acyclic proof. The plan records the actual selected rules and their new topological order; every emitted parent again precedes its child.

The immutable input remains [Source 149’s certificate](../lean217/dominated_rho8_full_certificate.json), SHA-256 `3cf18a5fe9f187b50b79d97b84535ce9bf776305728b0cdfe17285e94f028452`. It is neither replaced nor edited. The 18,669-byte [plan](plan.json) gives 629 original node IDs in order and 179 rule overrides using original node and term IDs. Unlisted rules are taken verbatim from the original certificate. Overrides are exact substitution instances; zero normalization uses only `Imp(T,T)=T`.

[replay.py](replay.py) needs only Python’s standard library:

```sh
python3 replay.py ../lean217/dominated_rho8_full_certificate.json /tmp/rho8-629.json
```

The destination must be new. The replay checks the original hash, all selected dependencies, every override’s normalized substitution, the term/node counts, and the final output hash. It emits a 72,525-byte `term_dag_v1` certificate with 939 input terms, SHA-256 `eb2970e1e4b86c1f0d26ec81bab59373e56f596f5c6359d57beec920cc6994bf`. Its `sources.original` string preserves the original discovery workspace path as historical metadata; it is not used to locate an input or establish validity.

For generator integration, `replay(original_bytes, plan_dict)` returns those exact bytes. Apply the default plan only when the input has the pinned Source 149 hash; other inputs retain the generator’s generic behavior. An explicitly requested plan must satisfy its own input hash. The renderer then checks/emits ordinary proof steps as before. Neither the plan, matcher, optimizer nor Python replay is trusted by Lean or Rocq.

The search used a bounded AND/OR integer program with a node for each original theorem, a choice among valid proof rules, and rank constraints forbidding cycles. The numerical solver reported 629 optimal in this finite rule family. That report is discovery evidence only, not a kernel-certified lower bound. Reproduction of the maintained proof needs no solver, SciPy, or optimization run.

An independent finite checker validated every rule and the exact original target, with the original 3,728-node and previous 674-node certificates as controls. Its first draft omitted the delivered `mp_substitution` convention: after instantiating both premises, the consequent may be injectively renamed. The corrected checker and both failed controls are retained with the search evidence. The candidate itself was unchanged by this checker correction.

The original certificate and mathematical construction are Source 149’s contribution. The earlier-schema reduction, global sharing search, deterministic plan, independent finite checks and kernel integration are repository follow-up work. The exported `DomImp` and `rho8_all` statements retain their existing scope and assumptions.
