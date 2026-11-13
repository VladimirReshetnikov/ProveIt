# Fixed-byte degree certificates for package 72

The independent [checker](check.py) reads the pinned P13 and P14 graphs and
their two pinned active bindings. It follows the now-restored declared port
paths, verifies compressed/raw hashes, lengths and little-endian bit lengths,
and checks byte identity against the source44 payloads. The separate
[restoration packet](../p72-compact-port-path-restore/README.md) records that
all four declared paths were absent before repair. MF is already shifted and
is not shifted again.

All four ports **and six beta-derived leaves** are treated as fixed integer
constants for operation-count and witness-degree purposes. The checker
expands each graph residual exactly over the integers with four symbolic port
variables and packed exponents; it first proves its exponent packing cannot
overflow by a gatewise bound. It independently checks the complete finalizer
is the sum of residual squares. Thus the exact symbolic residual degrees give
an integer upper bound: P13 has degrees 13, 13, 13 and 14, yielding degree at
most 28; P14 has degrees 12, 11, 12, 12 and 2, yielding degree at most 24.
Naive gatewise propagation without cancellations would give the weaker 36
and 32 bounds.

For the lower bounds the checker substitutes the same indeterminate `t` for
all witnesses, evaluates the entire graph with the actual restored fixed
bytes modulo 1,000,000,007, and obtains nonzero leading coefficients
148,768,232 at degree 28 and 925,559,841 at degree 24. These certify exact
integer degrees for those bytes. It checks all 98 and 101 gates and operation
breakdowns. This is external finite arithmetic, not a Lean degree theorem or
a Lean interpretation of serialized files.

The checker exited 0 and produced [result.json](result.json). Its SHA-256 is
`7129fb6b47638d5eb979b84c71cfc7c2fb47bb6e58ef7a012fba6010f2047936`;
the result SHA-256 is
`bdc18bf9ab7fe29835617860173ee0f4041abffa0fd9de514398ac968e82e993`.
Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/p72-fixed-byte-degree-certificate/check.py
```
