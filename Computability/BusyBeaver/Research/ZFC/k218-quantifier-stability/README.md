# K/S with quantified stability recovers the classical native calculus

Replacing unrestricted rho8 by K, S, and
`NN(Q_i A) → Q_i A`, while retaining all other exact KCode222 rows,
gated bundles and rules, preserves **every derivable native code**.
The [ordinary proof](proof.md) supplies both proof translations. Its
new direction derives atomic stability from the retained rows, then uses
strong induction on native codes to obtain unrestricted double-negation
elimination and recover rho8. Native truth zero and `I(0,0)=0` are handled
explicitly. Every generalized premise is a closed theorem.

The author-built [Hilbert checker](check_derivation.py) passed on its
second attempt and produced [2,134 proof nodes with 18 closed outputs](result.json).
The first attempt's Python name-shadowing failure is retained under
[history](history/attempt1/repair.diff). An [independent review](peer/review.md)
read the complete argument and independently checked all saved proof nodes
without rerunning the author builder; it found no defect.

This is ordinary mathematics with executable proof-DAG evidence. It is not
a Lean/Rocq endpoint, a retroactive calibration of K/S alone, or a smaller
machine. Exact source enumeration, allocation, runtime and startup checks
remain necessary for any candidate using these replacement rows. The accepted
[K218 construction](../candidate-k218/README.md) retains its original
classical rho8 and does not depend on this new result.

The submitted Source144 supplement supplied the K/S-only atomic-stability
lemmas and identified quantified stability as the remaining obstruction.
Root proposed adding the explicit quantified-stability row. `opening_encoder`
authored the complete calibration proof and finite checker;
`review_upstream_reflection` independently reviewed both. Exact bindings to
the native definitions, submitted supplement and preserved execution are in
[freeze.json](freeze.json) and [publication.json](publication.json).

For reproduction, use a new scratch directory so the recorded evidence stays
unchanged:

```sh
mkdir /tmp/k218-qs-check
cp Computability/BusyBeaver/Research/ZFC/k218-quantifier-stability/check_derivation.py /tmp/k218-qs-check/
python3 -B /tmp/k218-qs-check/check_derivation.py
```

The output is a fresh `result.json` and `proof-dag.json`; no compiler, solver,
network access or proof-assistant tool is needed.

The simpler **uniform DNE** replacement, K/S plus `NN A→A` for every
native code A, is an immediate corollary. The conditional rho8 proof already
checked here uses exactly stability of its code C, so the new DNE axiom supplies
that premise directly. Conversely the original classical calculus proves
K/S/DNE. This uniform row is distinct from the previously uncalibrated fused
proposal `NN(Q_i A)→A`. No new compiler or state-count measurement for either
replacement is claimed in this packet.
