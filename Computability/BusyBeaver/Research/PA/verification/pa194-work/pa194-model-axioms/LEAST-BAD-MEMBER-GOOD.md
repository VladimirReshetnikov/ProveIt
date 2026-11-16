# A member below the least bad point is good

For arbitrary internally valid property `p` and model-valued indices `s`, `b`, `m`, the constructor consumes contextual proofs of the opened separation trace of `¬p`, `m ∈ shifted-s`, the universal least-exclusion theorem, domain(b), least(witness,b), and m ∈ b. It constructs a proof of shifted-p(m) in the same context. The witness is free variable 0 and shifted-s is free variable `s + 1`. The construction combines the actual reverse trace-membership implication with least-point exclusion and a contradiction cut. A fixed parameter-free Σ₁ graph computes exactly its internal proof code, including for nonstandard properties, indices, contexts and proof codes.

`leastBadMemberGoodFromTheory` supplies the universal least-exclusion theorem using the classifier-defined full adjunctive separation theory and model-level choice, leaving the five other derivations as hypotheses. No uniform graph is claimed for selecting that theorem proof. In particular, deriving `m ∈ shifted-s` from transitivity, the complete minimum-bad contradiction, ordinal induction sequent and native iPRA equivalence remain open.

From the repository root:

```sh
Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-least-bad-member-good.sh "$PWD" /dev/shm/pa194-least-bad-member-good-repo
```

The checker rebuilds the source against prebuilt dependencies, verifies direct hashes, checks four axiom reports and rejects `sorryAx`; the reports list only `propext`, `Classical.choice`, and `Quot.sound`.
