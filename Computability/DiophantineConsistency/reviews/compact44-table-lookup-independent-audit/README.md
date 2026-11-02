# Independent compact-specific bounded lookup audit

This reviews paired evidence `0a5f299b08`. In any IΣ₁ model, for the exact
finite Lean arrays from the audited table correspondence, the six compiled
statements give:

- horizontal lookup injectivity for indices below 250 and surjectivity onto
  values below 250;
- vertical lookup injectivity below 439 and surjectivity onto values below 439;
- old-row-index lookup injectivity below 942, and surjectivity onto values
  below 943 **other than 1**.

These are bounded model lookup statements. Their proofs use that a model
element below a standard finite bound is a standard numeral; they do not
assert that the entire model is standard. The source's `tabValue` tables use
the displayed finite arrays and the omitted compact row 1 is explicit.
The finite JSON-to-Lean table/array association remains an external checked
source-data bridge. No theorem here provides matching neighboring modeled
cells or wrap, transports an arbitrary model tiling, calibrates the compact44
checker, simulates a machine, or establishes an iPRA endpoint.

The read-only audit checks both committed parent audit receipts, reruns their
full audits, and checks each paired source/object/log and direct-import row.
For each side, all 1,149 common `.olean` paths of the table and generic-lookup
providers are compared together with all ten present/absent companion hashes;
the independently reconstructed overlap-manifest digest matches the receipt.
The table overlay and copied generic seed are checked, as are all 50 direct
companion realpath/hash-or-absence guards. Outer session 33946 and both
compiler and `--deps` exits are recorded as zero; sibling objects and logs
match. All six exact named axiom reports list Lean metatheory `propext`,
`Classical.choice` and `Quot.sound`; the successful logs have no warning,
error or `sorryAx`.

The terminal observation records a clean-loader invocation; this audit checks
that record, not an independent continuous environment history. Inherited
Foundation outer-wrapper, package-transitive and dynamic ancestry limits
remain. The compiler RSS/disk monitor is sampled, not a hard process-tree
quota; `--deps` and audit subprocess timeouts are not whole-tree resource
bounds. Hash checks are point-in-time; reruns require the original `/tmp`
object trees. No Lean compiler is started by this audit.

Run from the repository root:

```
python3 -I -S -B Computability/DiophantineConsistency/reviews/compact44-table-lookup-independent-audit/audit.py
```

Actual read-only audit session 75949 exited 0; the committed script has the
same bytes as the version run from `/tmp`. See `CHECK.json` and
`terminal-observation.json`.
