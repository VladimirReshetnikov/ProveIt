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

The ledger is conservative.  Existing Coq developments elsewhere in `ProveIt`
may establish mathematically related results, but they are not marked as a
Foundation module port until their statements and dependency boundary have
been compared explicitly.

## Declaration-free facades

| Coq facade | Foundation source | Ported boundary |
| --- | --- | --- |
| `Foundation.Init` (`Coq/Init.v`) | `Foundation/Init.lean` | Exact empty facade for a source module containing no imports or declarations |
| `Foundation.Modal.Kripke` (`Coq/Modal/Kripke.v`) | `Foundation/Modal/Kripke.lean` | Exact import facade over all 26 unique source imports, represented by 29 existing checked Coq modules. Coverage remains partial only at the documented `Balloon`, `GrzPoint3`, `KTMk`, and `S4H` boundaries |

The incompleteness port also includes `Coq/FirstOrder/Incompleteness/Examples.v`.
It checks all seven strict-theory examples through explicit coding, extension,
and truth adapters, so the missing concrete PA/ISigma1 arithmetization boundary
is visible in theorem hypotheses rather than silently assumed.

Generic ports that are shared across Foundation's first-order, second-order,
and linear-logic trees live under `Coq/` with logical root `Foundation`.  Build
and kernel-check that project independently with:

```powershell
coq_makefile -f Logic/FoundationPort/Coq/_CoqProject `
  -o Logic/FoundationPort/Coq/Makefile.coq
make -C Logic/FoundationPort/Coq -f Makefile.coq Audit.vo
rocqchk -Q Logic/FoundationPort/Coq Foundation Foundation.Audit
```
