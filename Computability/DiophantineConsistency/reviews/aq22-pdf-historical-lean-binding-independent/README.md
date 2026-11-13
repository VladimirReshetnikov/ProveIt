# Independent AQ22 historical PDF-binding review

The independent review exited zero and reproduced the results of the
[original finite binding checker](../aq22-pdf-historical-lean-binding/README.md)
in a temporary sibling directory, using an exact copy of its script. The
original checker independently rejected six literal mutations and four port
digit mutations. Both the copied original and this independent checker
rejected optimized Python. The [terminal observation](terminal-observation.json)
records this review's actual process exits; the nested original-checker exits
are in the [receipt](receipt.json).

This review parses the historical Lean literal into ordered variable and port
bindings and 114 arithmetic operations, and compares them with the pinned
candidate graph. It checks the exact standard-theory endpoint statement,
including its Gödel–Gentzen translated selected Foundation consistency
sentence, the positive-shift definition, the historical source hashes, and
each recorded import-object hash on the paths to the literal and port provider.
It compares the entire saved decimal `#eval` output of each of the four ports
with its full decompressed integer coefficient and recorded independent port
probe. The saved probe and historical AQ22 author use the same pinned parent
state and `CurrentKernelData2011` object. The prior independent port review
records a fresh probe exit 0 and a separate reconstruction exit 0.

The original review's earlier independently audited display and wording
receipts support the graph-to-TeX and TeX-to-PDF links, including the graph's
114 printed gates; this review does not independently interpret arbitrary
TeX or rerun those display generators. The fixed decoder, tile table, rank and
port recipe remain manually transcribed into a finite checker. The saved
`#eval` and numeric comparisons are external computations, not internal Lean
theorems about TeX or PDF semantics. Neither this review nor its checker
reruns the Lean endpoint or the port probe. The result is historical, with one
author build and no matched AQ22 peer replay; it inherits the stated
package-transitive, dynamic-load, transient-mutation, and missing outer
Foundation-wrapper-exit limitations.

Run with ordinary Python from the repository root after moving only this
packet's receipt to a safe temporary location, restoring it afterward:

```sh
python3 Computability/DiophantineConsistency/reviews/aq22-pdf-historical-lean-binding-independent/verify.py
```

The checker refuses to overwrite its receipt and requires the original
historical `/tmp` parent state and frozen sources to remain available. Its
receipt is evidence for the recorded hashes at the time of the run, not a
claim that these temporary files persist.
