# Reconstruct a bounded natural number from its digit windows

`RadixWindowReconstruction.ofDigits_eq_of_windows` is a Lean theorem for
arbitrary base `b ≥ 2`, natural `n`, and finite list `xs`. If

```
n < b ^ xs.length
∀ i < xs.length, xs.getD i 0 = n / b^i % b
```

then `Nat.ofDigits b xs = n`. The theorem accepts leading zero digits and
does not need a separate digit-range assumption: the window equalities
already force the listed values to be valid base-`b` digits. It uses a
generic lemma showing that padding a standard digit list with zeroes does not
change any default-zero lookup, list extensionality, the standard digit
window identity, and reconstruction from padded digits. No specific large
number, finite certificate, file or compressed data is evaluated in the
proof.

This theorem supplies the *assembly step* needed for a future retained MC
byte binding: prove the actual proposed Lean byte literal's windows match
those of the symbolic low mask, in bounded chunks, and prove that the mask
is below `256 ^ literal.length`; then apply the theorem. Neither premise is
proved for the retained MC payload here. In particular, the theorem does
not identify any file bytes, gzip output, symbolic coefficient, JSON, PDF or
an iPRA endpoint. Any external file-to-literal generation and checking must
be separately documented or formalized.

The bounded author run `observations/attempt01` exited 0 in 1.815 seconds
with no warnings or `sorryAx`; its recorded direct dependency/companion
guards were unchanged. The source SHA-256 is
`34c46f6523b4d69b6487e8e2ac7e6f7de21845ee6f7b0b3f0e0b913f794c6add` and
the output object SHA-256 is
`0ebcfad8f9de63908c10c280d877c73684b4a98ae41c2ceeddab7914fa8dd62f`.
For both named theorems Lean reports `[propext, Classical.choice,
Quot.sound]` as metatheory dependencies; these are not object-theory axioms.
The exact source copy, logs, dependency output, guards and terminal receipt
are retained. This is a single author-side check over inherited package
objects, not a paired replay or full project/package/dynamic ancestry audit;
guard checks are point-in-time.
