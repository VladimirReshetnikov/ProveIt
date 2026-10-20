# K does not repair membership-fourth rho8

A three-value algebra validates the exact native calculus obtained by replacing
unrestricted rho8 with `rho8(A,B,C,R(A,B))` and adding every K instance. It also
validates every quantified-stability instance `NN(Q_i A) → Q_i A`. The full
retained rho1–6, merged G, literal gated seed bundle, truth, MP and theorem-only
GEN remain present. Nevertheless native falsum is undesignated.

The [ordinary proof](proof.md) defines a primitive-recursive valuation on **all
natural codes**, including the zero alias `I(0,0)=0`. Membership is evaluated
from the recursively obtained values of its two numerical labels. This is a
syntactic algebraic valuation, rather than a Tarski interpretation of free
variables. The literal seed bundle's private label and matrix are both the
same code; preserving that coupling is essential to the proof.

This gives an elementary consistency proof, formalizable in PA. Thus, assuming
ZFC is consistent, no ZFC proof can identify this calculus's consistency with
Con(ZFC). This is stronger than the earlier bounded searches' failure to find
classical derivations. It is an ordinary mathematical result, **not a newly
checked Lean or Rocq theorem**.

The [separate finite checker](check_model.py) actually passed and produced
[the certificate](model-check.json). It checks every carrier assignment to the
literal rows and complete bundle, MP/GEN preservation, and concrete schema
failures. The all-natural conclusion comes from the recursion and proof
induction in the ordinary proof, rather than finite code sampling. An
[independent peer](peer/review.json) read the entire proof, checker and exact
native definitions without rerunning the author's code and found no defect.

This model rejects `F → F`, whose native numerical code is 16. It also rejects
composition B and S at the concrete parameter codes `(1,16,1)`. Consequently
neither a general deduction theorem nor arbitrary implication-context
transport may be assumed in this calculus. The earlier five-node theorem
`(T → C) → (B → C)` is valid but does not supply that transport.

Adding the single axiom code 16, all identities, B, S, or some other axiom that
fails this model escapes **this particular obstruction**. None of those
extensions is calibrated here. In particular, the separate
[K/S plus quantified-stability calibration](../k218-quantifier-stability/README.md)
is unaffected because its S row fails this model. The accepted
[218-state candidate](../candidate-k218/README.md) keeps its original calculus;
this packet makes no source-cost or smaller-machine claim.

Source147's submitted five-value model motivated the search but fails K.
`opening_encoder` authored this new code-dependent algebra, ordinary proof,
search and independent literal-expression checker. `review_upstream_reflection`
performed the independent source review. Exact native source snapshots,
original logs, discovery output and inventories are retained in
[freeze.json](freeze.json) and [publication.json](publication.json).

To check the certificate in a fresh directory, from the repository root:

```sh
mkdir /tmp/k218-k-rab-check
cp Computability/BusyBeaver/Research/ZFC/k218-k-membership-obstruction/check_model.py /tmp/k218-k-rab-check/
cp Computability/BusyBeaver/Research/ZFC/k218-k-membership-obstruction/search3-d1.json /tmp/k218-k-rab-check/
python3 -B /tmp/k218-k-rab-check/check_model.py
```

The checker writes fresh `model-check.json` and `literal-rows.json`. It imports
no search code and needs no compiler, network access or proof assistant.
Reproducing the stochastic discovery is optional: compile `search.cpp` with
`g++ -O3 -std=c++17`, then run the resulting executable with arguments
`12 3 1 218` (seconds, carrier size, designated-value count, seed). Wall-clock
and proposal counts are diagnostic, not proof evidence.

A [separate bounded follow-up](fixed-code16/README.md) added the single fixed
axiom code 16. Three small matrix searches found no candidate; this extension
remains open, and the diagnostic is separate from the proved obstruction.
