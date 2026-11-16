# A member below the least bad point is good, using transitivity

For arbitrary internally valid property `p` and model-valued indices `s`, `b`, `m`, the constructor consumes contextual proofs of the opened separation trace of `¬p`, the universal domain-transitivity theorem, the universal least-exclusion theorem, domain(shifted-s), b ∈ shifted-s, domain(b), least(witness,b), and m ∈ b. It derives shifted-p(m) under the same context, first deriving m ∈ shifted-s by domain transitivity and then applying the previously checked least-bad member-good construction. The witness is free variable 0 and shifted-s is free variable `s + 1`. A fixed parameter-free Σ₁ graph computes exactly the internal output proof code for nonstandard property, index, context and proof inputs.

`leastBadMemberGoodTransFromTheory` supplies both fixed universal theorems using the classifier-defined full adjunctive separation theory and model-level Lean choice. Its other six derivations remain hypotheses, and no uniform graph is claimed for selecting the theorem proofs. The complete minimum-bad contradiction, ordinal induction sequent and native iPRA equivalence remain open.

From the repository root:

```sh
Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-least-bad-member-good-trans.sh "$PWD" /dev/shm/pa194-least-bad-member-good-trans-repo
```

The checker rebuilds the source against prebuilt dependencies, verifies direct hashes, checks four axiom reports and rejects `sorryAx`; the reports list only `propext`, `Classical.choice`, and `Quot.sound`.
