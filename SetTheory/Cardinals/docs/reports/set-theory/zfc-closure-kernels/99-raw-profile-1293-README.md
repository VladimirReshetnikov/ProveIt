# Context-dependent state 18 addendum

The general theorem in `state18_context_addendum.tex` proves that existing
state 18 implements increment of logical N when its pointer ends in 1 or
10, or is the singleton 0 with its preceding marker. The proof reduces each
zero pulse to the previously proved generic pulse and retains the inherited
register and scanner induction contracts. No transition or state changes.

The same file gives the derived incoming-mask recurrence and records an
independent review of `derived_mask` and `context_ok` in the grammar worker's
`anneal_fine_contextual18.cpp`. This review is conditional on the ordinary
atomic contracts. Full compiled-table and initializer verification remains
necessary.

Run the exact local premise checker with an explicit Routing245 table:

```sh
python3 check_state18_context.py /path/to/zfc245_old.tm
```

The successful checked local traces read no cell outside their declared
two-cell or three-cell window. Thus their tape-preservation conclusion is
independent of all unspecified tape cells. The complete instruction proof
still uses the inherited unbounded register and scanner contracts.

## Serialization correction to the frozen runtime README

The frozen runtime packet's `reference/machine/zfc245_old.tm` is the
6425-byte inherited serialization, with SHA-256
`f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267`.
The frozen README instead quoted
`df61b22c3152a14a3be31cf789be47b572d56bd7b106cd42e3a96ffd834ebe98`,
the SHA-256 of the 6426-byte fetched serialization used during exploration.
All 490 parsed transition rows are identical. The frozen reference manifest
already records the correct hash for its file. This addendum leaves the
frozen packet unchanged and records the distinction explicitly.
