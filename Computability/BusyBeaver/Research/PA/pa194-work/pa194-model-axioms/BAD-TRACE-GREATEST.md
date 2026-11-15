# Greatest predecessor for a bad-trace member

For every internally valid arity-one `p` and model-valued `s`, `x`, the constructor consumes contextual proofs of the opened separation trace of `¬p`, x ∈ witness, the fixed member-domain theorem, the fixed nonzero-domain greatest-element theorem, domain(shifted-s), and the ordinal base statement for shifted p. It derives `greatestExists(x)`: trace membership and downward closure give domain(x), the bad property and base case give ¬zero(x), and the greatest-element theorem provides the existential. A fixed parameter-free Σ₁ graph computes the exact output internal proof code for nonstandard property, index, context and proof inputs.

`badTraceGreatestFromLogic` supplies both universal theorems from fixed pure-logic proofs using model-level Lean choice, leaving the trace, witness-membership, shifted-source-domain and base derivations as hypotheses. No uniform graph is claimed for selecting the theorem proofs. The existential witness branch, complete minimum-bad contradiction, ordinal induction sequent and native iPRA equivalence remain open.

From the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-bad-trace-greatest.sh "$PWD" /dev/shm/pa194-bad-trace-greatest-repo
```

The checker rebuilds the source against prebuilt dependencies, verifies direct hashes, checks four axiom reports and rejects `sorryAx`; the reports list only `propext`, `Classical.choice`, and `Quot.sound`.
