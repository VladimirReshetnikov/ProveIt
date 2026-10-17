# Bounded-support diagnostic

From the artifact root:

```sh
python3 -B code/theory/support_diagnostic.py
```

For a complete JSON result, supply `--output /tmp/support-results.json`.
Python 3.10+ and its standard library suffice. Assertions must be enabled.

The diagnostic checks 226,440 exact three-factor stabilizer decompositions
in Sym(6), 2,880 nested Kuratowski-code stabilizer comparisons, and 71
explicit witnesses against support sets that are too small. It also checks
negative controls for noninjective equivariant maps, orbit quotients, and
the failure of support intersection for complementary large supports in a
finite symmetric group.

This is a finite algebra diagnostic, not a finite EPSC1 model, consistency
evidence, or a proof of the infinite-group theorem. The mathematical proof
and its application to all fixed finite-dimensional interpretations are in
Section 3 of report.pdf and sections/03_support.tex. The standard support
facts are attributed to Andrew Pitts's 2011 Nominal Sets lecture notes;
the application to the incoming unary model is new relative to the inspected
ProveIt snapshot, without a worldwide priority claim.

The saved result is data/theory/support_results.json. The direct BU/AU raw
deductive equivalence is an ordinary proof in Section 2; no machine-checkable
proof-code transformer for that theorem is claimed by this script.
