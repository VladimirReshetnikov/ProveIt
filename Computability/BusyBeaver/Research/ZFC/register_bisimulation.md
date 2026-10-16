# Register-operation bisimulation

`../../Lean/BusyBeaver/ZFC/RegisterBisimulation.lean` proves a generic
certificate interface for deterministic register programs. Registers are
arbitrary functions `Nat → Nat`. Instructions increment one register,
conditionally decrement one register, or halt. A zero decrement leaves the
register vector unchanged; a positive decrement subtracts one.

The hypothesis `Matches p q relation` requires each related instruction pair
to have the same operation and register index. Increment successors must be
related, and **both** the zero and positive successors of each decrement must
be related. Halt instructions must match halt instructions. Under this
hypothesis, `run_related` preserves the state relation and equality of register
vectors. `run_none_iff` proves halting at the same finite attempted-operation
count, and `halts_from_any_registers` proves halting equivalence from every
common register vector, including vectors retained between proof candidates.
The relation need not be a function or a bijection.

The counting convention is explicit: `run p 0 c = some c`; encountering a halt
instruction returns `none` on the next attempted operation. These counts do
not include decoder or control paths contracted into an exposed register
instruction.

This is the generic theorem needed after checking a finite relation such as
the submitted 3,394-pair register-machine relation. This module does **not**
instantiate that relation, validate its instruction tables, justify exposing
instructions from the original DAG, prove any decoder/control contraction, or
connect either register program to a binary Turing machine. It proves no
ZFC-consistency endpoint.

The file imports only `Init` and compiled with:

```sh
LEAN_PATH=/tmp/zfc-lean-check-2phtash2 lean \
  -o /tmp/RegisterBisimulation.olean \
  Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RegisterBisimulation.lean
```

The source itself has no project imports, so the cache path is incidental to
this invocation. The four printed axiom reports (`step_related`, `run_related`,
`halts_iff`, and `halts_from_any_registers`) contain only Lean's standard
`propext`; there are no custom axioms or `sorry` declarations.
