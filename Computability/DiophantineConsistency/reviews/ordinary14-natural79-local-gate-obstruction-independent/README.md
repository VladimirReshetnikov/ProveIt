# Independent review: local one-gate output-identity obstruction

The reported finite exclusion reproduces. A separate arithmetic-AST parser
checks all 79 selected Lean graph rows, input/port aliases and returned graph
fields against the pinned candidate. The independent checker verifies the
four P72 coefficient payloads against their raw and compressed hashes and the
P115 binding, reconstructs the explicit natural witness, and obtains the
reported original output residue modulo `2^61-1`.

The independent enumeration identifies the same 55 eligible parent/child
pairs and 1,084,128 operand/operator tuples. It counts consumer **nodes**,
including a parent that uses a child twice, and excludes the deleted child from
the available earlier operands. For each of the 41 distinct parent gates, it
constructs an exact univariate output polynomial over integers modulo the
specified modulus, with the new parent value as the indeterminate. It checks
that substitution of the original value recovers the original residue, then
exhausts all candidate operation values. The zero survivor count agrees with
the author's differently implemented downstream reevaluation; both receipts
reproduce. No primality assumption is needed.

One modular disagreement at the explicit natural input is a valid witness
against equality of the corresponding fixed-port integer output polynomials.
The result is restricted to the described local class: it does not rule out
other rewrites, different constants, witness changes or another 78-operation
Diophantine equation. Nor does an unequal output value imply different zero
sets. The retained byte identity with the Lean symbolic ports and any physical
page semantics remain separate from this finite computation. No Lean or staging
was performed.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural79-local-gate-obstruction-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural79-local-gate-obstruction-independent/result.json
```
