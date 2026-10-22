# Origin of the guarded CB1 pilot

`CB1Suffix.original.lean` is the exact source-only draft retained in the
phase-nine evidence archive at the pinned ProveIt commit:

```text
Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase9/lean/execution.tar.gz
```

Archive member:

```text
context/uncompiled-cb1/CB1Suffix.lean
```

The adjacent upstream `index.json` records 4,773 bytes and SHA-256:

```text
c1b75270d25f61fd6720c6469f2fdda6f6b6d21d28f2d12eb623e68d7d119240
```

The preserved file has that exact size and digest. It is historical design
material and is **not** one of the accepted compilation targets. Its comment
stating that it was uncompiled is retained verbatim.

The checked successor is
`proposals/semantic_sites/proof/BusyBeaver/ZFC/KCB1Suffix.lean`. It repairs
list-association and gap-normalization details, and the new `KCB1Contract.lean`
instantiates it for the maintained table and semantic coverage interface.
The all-occurrence routing and guard theorem remains a separate obligation.
See the main report and the accepted semantic-sites ledger.

