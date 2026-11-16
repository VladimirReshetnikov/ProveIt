# Least-point exclusion at arbitrary internal indices

For arbitrary model-valued indices `c`, `b` and `m`, `leastExcludesAtProof` consumes contextual proofs of the fixed universal least-exclusion theorem, domain(b), least(c,b), and m ∈ b. It constructs a contextual proof of m ∉ c. The input and output instances are the exact substitutions of explicitly named three-variable templates at `[m,b,c]`. A fixed parameter-free Σ₁ graph computes exactly the resulting proof code, including for nonstandard indices, contexts and proof codes.

`leastExcludesAtFromTheory` supplies the universal theorem from the previously checked classifier-defined full adjunctive separation theory, leaving the three instance proofs as hypotheses. That fixed proof is selected from model-level provability using Lean choice; no uniform graph is claimed for the selection. The complete minimum-bad contradiction, ordinal induction sequent and native iPRA equivalence remain open.

From the repository root:

```sh
Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-least-excludes-at.sh "$PWD" /dev/shm/pa194-least-excludes-at-repo
```

The checker rebuilds the source against prebuilt dependencies, verifies direct hashes, checks four axiom reports and rejects `sorryAx`; the reports list only `propext`, `Classical.choice`, and `Quot.sound`.
