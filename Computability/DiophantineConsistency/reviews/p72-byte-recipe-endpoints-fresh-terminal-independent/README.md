# Independent terminal audit: P72 byte-recipe endpoints

The author-recorded outer receipt reports actual session **37484, exit 0**.
The retained dependency and compile runs separately report exit 0, with no
monitor stop, observed descendant or monitor error. The state SHA-256 is
`e6f65d1b0f174040abe9d64f8d0622395ea75b62217bf7b686e9453b402aa46c`;
the current output object under `/tmp/p72-byte-recipe-endpoints-fresh-20261105/`
is `eac163b2f9f9833e483be46ba87f3c48b7da6c0b051636dfed441665283d6c93`.
This reviewer did not independently observe the historical outer exit.

The compiled `byteP_eq_ports` identifies four closed Lean byte recipes decoded
by `Nat.ofDigits 256` with the symbolic ports used in the fresh P72 endpoints.
The fourth is the high-mask recipe shifted by beta once. The two endpoint
declarations then state that standard iPRA proves equivalence between no
natural zero of the respective positive-shifted P13/P14 expressions at those
ports and the mapped Gödel–Gentzen translation of the repository's ZFC
consistency sentence. Each of the three explicit Lean axiom reports contains
exactly `propext`, `Classical.choice`, and `Quot.sound`.

`check.py` rechecks both direct provider routes and objects, all 120 recorded
provider/companion guard slots, logs, source, object, and the author-recorded
outer receipt. The byte-port provider is the matching successfully compiled
fresh extension stage 609; the translated client is the separately audited
fresh terminal object. The state records matching pre/post hashes for the
independent 681-stage audit. This review does not rerun that audit, Lean, or
the separate base/archive checks.

These are Lean **byte-recipe** statements, not direct theorems about external
file contents, JSON, or the separate fixed-byte degree certificate. They do
not decide ZFC consistency. Base/package-transitive and dynamic-load ancestry,
between-observation changes and sampled-resource limitations remain.
