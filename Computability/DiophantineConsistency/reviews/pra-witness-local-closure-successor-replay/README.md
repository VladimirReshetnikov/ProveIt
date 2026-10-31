# Strict local-project witness closure after the omit fix

The predecessor rebuilt 205 local project modules from frozen source and then
stopped at `PRAWitnessSetTerms` because its `not_isFunc` theorem had an unused
`IΣ₁` instance warning. The failure state, log and original driver are kept in
`failed-predecessor/`. The fixed snapshot in `fixed/` adds exactly the linter's
suggested `omit` on that theorem.

The successor guards every object in the complete 205-module prefix and all
214 frozen source hashes, rebuilds the nine remaining modules, and rejects
Lean errors, warnings and `sorryAx`. It removes workspace project Lake object
fallback. At the author completion the 214 source hashes also matched the
workspace; this observation is time-specific and the replay itself consumes
frozen sources. It guards 18 direct Foundation/ZFC object anchors, but their
transitive ancestry, mathlib, toolchain and packages remain inherited.

Run:

```
python3 Computability/DiophantineConsistency/reviews/pra-witness-local-closure-successor-replay/replay.py
```

Author `/tmp/pra-witness-local-closure-successor-ppuiingq` and independent
same-parent `/tmp/pra-witness-local-closure-successor-qj4ojxc9` both passed;
all nine source/object/full-log rows match. They share the 205-module fresh
prefix, so the peer is not an independent rebuild of that prefix. States and
logs are frozen in `author/` and `independent/`.

The result establishes the local project closure through `PRAWitnessCodeGrowth`,
not the axiom recognizer, derivation core or PRA refutation certificate.
