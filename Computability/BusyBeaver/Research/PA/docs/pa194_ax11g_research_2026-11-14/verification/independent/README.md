# Independent literal-tape verification of AX11G

This checker imports no machine constructor and uses no arithmetic-box
oracle. It derives four generic unary-list traversal lemmas from the exact
candidate transition rows, then checks every source outcome over nine
arbitrary natural register values, both decrement branches, an arbitrary
finite nonempty spare list, and an arbitrary nonnegative affine header gap.
Two independent source-address resolvers must agree with the supplied
instruction graph. Dense/native conjugacy and the complete finite-support
blank-start tape are also checked.

The full successful replay checked 3,672 source sites and 4,779 outcomes in
1,083,079 symbolic operations. The maximum per outcome was 379 and every
physical duration had constant term at least three. Exact blank startup
took 58,154 transitions. These symbolic operation counts are proof-checker
costs, not upper bounds on arbitrary-register physical execution times.

Run, from the package root:

```sh
python3 -B verification/independent/check.py --output /tmp/pa194-ax11g-literal
```

With no positional argument the checker reads `../../machine` relative to
its own directory. An explicit machine directory can also be supplied.
Python 3.10+ and its standard library suffice. Assertions must be enabled.
A full replay can take several minutes.

`recorded/receipt.json`, `recorded/list_lemmas.json`, and
`recorded/startup.json` are the retained results. The complete per-outcome
certificate is losslessly compressed in `recorded/contracts.json.gz`.
The SHA-256 in the receipt is the digest of its uncompressed bytes. A fresh
replay writes the same substantive contracts as an uncompressed JSON file
under its chosen output directory.

The reference engine is copied unchanged from the pinned PA194G packet.
Only the candidate name, exact table hash, expected site/outcome counts,
and packaged default path differ in its wrapper. `PROVENANCE.json` records
the source identities and adaptations. The original reference README and
license notices are preserved; its historical path references are provenance
notes and are not additional dependencies of this self-contained checker.

These are executable mathematical certificates supported by the report's
symbolic induction argument. They are not a new Lean or Rocq kernel proof
of the absolute consistency equivalence.
