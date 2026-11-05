# Independent review: once-shifted current2011 MF decoder

The read-only [checker](check.py) exited 0 and produced [result.json](result.json).
It verifies the exact Lean theorem `decode_mf`: decode the reversal of the
explicit canonical big-endian byte list for `Nat.ofDigits rho maskDigits +
(rho^2011 - 1)`, and the resulting integer equals
`CurrentWindowCarry2011.ports 3`. The checked expression has **one** beta
shift. The named `shiftedValue` and `bigBytes` definitions in the final source
match those in the earlier draft after whitespace normalization; the high-mask
digit-list definition also matches the source evaluated by the external byte
checker.

The final proof composes a checked natural-sum identity, a checked cast and
port projection, `List.reverse_reverse`, and `Nat.ofDigits_digits`. The audit
checked all three successful child/outer sessions (46385, 63979, 80805),
their exact reports and objects, direct dependency routing and 180, 180 and
240 direct/companion/shadow guard slots. It checked the preceding failed
combined composition's outer exit 1 and excessive-memory diagnostic; that
failed artifact is not used as the final theorem.

The earlier [independent partial review](../current2011-mf-partial-binding-independent/README.md)
was rerun successfully. Its separate external checker evaluates the matching
high-mask recipe with beta added once and compares both retained MF payloads
byte-for-byte. Lean does **not** read or decompress those files; this remains a
Lean symbolic-list theorem plus an external file comparison. No K-port byte
binding, PDF semantics, independent second base rebuild, or complete
transitive/dynamic provider audit follows. No Lean replay was run here.

Reproduce from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/current2011-mf-decoder-independent/check.py
```
