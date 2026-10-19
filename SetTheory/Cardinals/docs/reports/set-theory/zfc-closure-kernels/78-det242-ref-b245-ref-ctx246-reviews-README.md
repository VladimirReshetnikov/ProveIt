# Optional independent 246-state audit

From the extracted package root, run:

```sh
python3 -B reviews/audit246.py reviews/prior250
```

Python 3.9 or newer and its standard library are sufficient. Assertions
must remain enabled: do not add `-O` or `-OO`. The `-B` option prevents
bytecode cache files. The only output file is
`reviews/audit246-results.json`, which is replaced beside the script.

The script is unchanged from the separate theory review. It reconstructs
the frozen 250-state table, applies the four-state reduction, checks
machine structure and exact transition-table hashes, reruns four block
inductions, three register macro inductions, nine marking inductions, and
all 8,391 guarded instruction cases from a fresh full parse of `Prog254.v`.
It also executes the exact 410,735-step blank bootstrap using separate
sparse and dense tape implementations and checks the complete final tape.

`prior250/` contains only the four required inherited Python modules,
the two source inputs they read, and attribution/license notices. No
network, source checkout, precomputed instruction-site cache, third-party
package, or file outside this directory is used. The dependency paths are
resolved from their module locations. To run from a different current
working directory, give paths to both the script and its dependency bundle:

```sh
python3 -B /path/to/zfc-context246/reviews/audit246.py /path/to/zfc-context246/reviews/prior250
```

This is an additional audit using the separately supplied prefix250
induction engine, not an independent implementation of that engine. A
successful run establishes the stated local symbolic checks and finite
bootstrap facts. Global composition and the connection to Con(ZFC) are
ordinary mathematical arguments described in the main report; this audit
does not compile a new Lean/Rocq endpoint or emit a formal ZFC derivation.
The inherited modules' standalone entry points belong to their original
larger package; this minimal subset is intended for `audit246.py` only.

See [prior250/ATTRIBUTION.md](prior250/ATTRIBUTION.md) for source pins,
byte hashes, credits, and the inherited license boundary.
