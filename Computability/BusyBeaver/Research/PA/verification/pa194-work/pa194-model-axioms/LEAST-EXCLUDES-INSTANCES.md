# Aligned least-point exclusion instances

For arbitrary model-valued indices `c`, `b` and `m`, the source proves exact typed equalities between the previously named three-variable domain and membership instances and the one-variable domain and free-variable membership syntax used by the ordinal-induction proof. `leastExcludesAlignedProof` uses them to derive m ∉ c from contextual proofs of the universal least-exclusion theorem, domain(b), least(c,b), and m ∈ b. Its proof code is exactly the previously checked fixed Σ₁ `leastExcludesAtCode` graph.

`leastExcludesAlignedFromTheory` supplies the universal theorem from the actual full adjunctive separation theory using model-level choice, leaving the domain, least and membership proofs as hypotheses. No uniform graph is claimed for selecting that fixed theorem proof. The least predicate remains in its explicit three-variable template syntax; the complete minimum-bad contradiction, ordinal induction sequent and native iPRA equivalence remain open.

From the repository root:

```sh
Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-least-excludes-instances.sh "$PWD" /dev/shm/pa194-least-excludes-instances-repo
```

The checker rebuilds the source against prebuilt dependencies, verifies direct hashes, checks six axiom reports and rejects `sorryAx`; the reports list only `propext`, `Classical.choice`, and `Quot.sound`.
