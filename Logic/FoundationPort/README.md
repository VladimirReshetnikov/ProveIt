# Foundation-to-Coq coverage ledger

This directory tracks the full port of the pinned, read-only
`FormalizedFormalLogic/Foundation` source tree.  Completion means accounting
for every Lean module and porting its mathematical results to independently
checked Coq; a green build for one subtree is not treated as repository-wide
parity.

The authoritative source inventory is the submodule itself.  `ported.tsv`
records modules for which work has begun or completed; every source module not
listed there is reported as `unported`.  Run:

```powershell
bash Logic/FoundationPort/coverage.sh > foundation-coverage.tsv
```

The command validates every mapping against the pinned tree, emits one row for
each of the 455 Lean modules, and prints status totals to standard error.  The
generated report is intentionally not committed because it is derived from
the gitlink and the small reviewed mapping file.

Status meanings:

- `ported`: the source module's theorem surface is represented by an
  independently checked Coq module, possibly with stronger generality or a
  more idiomatic proof;
- `partial`: a meaningful theorem slice is checked, but named results or a
  dependency layer from the source module remains;
- `unported`: no module-level parity claim has been reviewed yet.

The ledger is conservative.  Existing Coq developments elsewhere in `Proofs`
may establish mathematically related results, but they are not marked as a
Foundation module port until their statements and dependency boundary have
been compared explicitly.
