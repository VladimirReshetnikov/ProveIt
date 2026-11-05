# Current2011 13-variable 70/140 and 71/128 forms

The two [70-row](polynomial70.json) and [71-row](polynomial71.json) integer
graphs reuse the exact gate lists from the independently documented older
2471-port forms, with the **different current2011 port tuple** from the
retained 13-variable 75/96 graph. All 13 positive witnesses, four integer
ports, and all listed binary gates are live. The 70-row form uses 39
multiplications, 16 additions and 15 subtractions; the 71-row form uses 40,
16 and 15 respectively. These are straight-line positive-coordinate counts,
before the shift used in the iPRA syntax, not minimality claims.

The [checker](check.py) compares each complete graph output with the
`ModelThirteenForms.expressionAt70` or `expressionAt71` source, using the
`ModelThirteenCarrier.front13` source. It normalizes addition and
multiplication for associativity and commutativity and uses exactly one
documented distributive cut, `Delta*f² - Delta = Delta*(f² - 1)`. It checks
the source and graph pins, witness order, row topology and liveness, all four
recorded port payloads, and the parent source receipts. This is an external
source-level comparison; Lean does not read these graph files.

For each fixed-byte graph the checker derives an upper bound by ordinary
degree propagation, except that it uses the exact main-norm cancellation

`N1 = X² + 2*X*a*c + 2*gamma*H*(X+a*c) + gamma²*H² - H*c²`

to bound `N1` by degree 18. The checker verifies all rows required for that
identity. Independently, it substitutes one variable `t` for all 13
witnesses, substitutes the actual recorded integer port bytes, and evaluates
the complete graphs over the field with 1,000,000,007 elements. The leading
coefficients of `t^140` and `t^128` are respectively 171,890,737 and
39,067,118, both nonzero. Thus the stated exact degrees hold for the
recorded fixed integers. These are finite external checks, not Lean
`totalDegree` theorems or proofs that serialized payloads equal Lean ports.

The exact source expressions have existing no-premise standard-iPRA
mapped-refutation endpoints, with `CurrentWindowCarry2011.ports`, checked in
the [paired lower-degree suffix](../thirteen-model-lowdegree-suffix/README.md)
and its [independent review](../../reviews/thirteen-model-lowdegree-suffix-independent-audit/README.md).
The suffix compiled `ModelThirteenForms` twice from source SHA-256
`98d9dcc48895ffe026c029b2496a61a35b66bca2f7b2fd1b31b8acf43acbfb6f`
to identical object hash `2d881b56c3c7677f8488658b406f80b5da01cb8212cf4ffa103bffb4521a31e4`.
Its recorded direct `ModelThirteenCarrier` inputs agree with both preceding
successor records, whose source hash is
`57f3cf755891aa921e9d97877af373e9194c6aa709a259c47678e4a370fd0185`.
The paired receipt and its separately observed outer exit are checked here.
This is a connection to **historical recorded builds**, not a Lean check of
these JSON files or a complete dynamic or package-transitive ancestry audit.
A later [fresh-base Forms build](../thirteen-current2011-forms-4g/README.md)
and [endpoint report client](../thirteen-current2011-final-checks-4g/README.md)
check the two standard-iPRA mapped-refutation declarations; their [independent
review](../../reviews/thirteen-current2011-final-checks-4g-independent/README.md)
records the source and provider scope. Graph/file comparisons and the degree
claims remain external.

A fresh rerun of the historical independent audit was attempted and exited 1;
its tool output named a missing `ZFCinPA/NativeGicDelta1.olean`. A second
rerun was captured to preserve stderr and also exited 1, this time naming the
missing `DiophantineConsistency/HerbrandGeneratedSubmodelTriple.olean`. Its
observation and stderr are retained in [`historical-audit-attempt01`](historical-audit-attempt01/).
The audit iterates a set, so different missing files may be encountered first.
This does not
retroactively invalidate the earlier recorded run, but means that run was not
reproduced now and that this packet does not assert a currently available
coherent historical provider.

The [result](result.json) was produced by running from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/thirteen-current2011-forms-frontier/check.py
```

`build.py` recreates the two graph files from the pinned gate lists and
current2011 metadata and refuses to overwrite either. Neither checker nor
builder invokes Lean. The maintained `equation.tex` and `equation.pdf` are not
modified. Independent review of this new graph/source and degree check remains
necessary.
