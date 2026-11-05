# Lean binding of the 66-row rational evaluator to the 67/106 syntax

The generated Lean file checks the complete 66-row and 67-row graph outputs
over **any commutative ring**. Under the two explicit fixed-leaf equations
`beta * Urank = MF` and `Wrank = MC - MF`, `values_equal` proves their
pointwise equality. `value67_eq_syntax` binds the full 67-row output to
`ModelCarrierCurrent.expressionAt106`; `value66_eq_syntax` composes the
two facts for integer ports cast into the ring and arbitrary ring-valued
inputs. These are polynomial evaluation statements, not model-theoretic
or internal iPRA statements about rational constants.

The proof uses a small abstract `strong_factor` ring identity to reconcile
the graph's `i²*delta*c⁴` product with the syntax's `delta*(i*c²)²`,
without globally normalizing the large expression. `audit_rows.py`
independently checks the generated literal source rows and aliases against
the frozen 66- and 67-row JSON: 28+5+33 and 28+6+33 respectively. The
underlying rational graph's exact Laurent identity, fixed current2011
leaves and 53,223-byte separate-magnitude accounting are in
`../normalized106-rational66/`.

Attempt03 passed: Lean and runner exit 0, no warnings or `sorryAx`; axiom
reports are `[propext, Quot.sound]` for `values_equal` and
`value66_eq_syntax`, and `[propext]` for `value67_eq_syntax`. The run used
`-M2800`, 120 seconds, sampled 3.5 GiB process-group RSS and 10 GiB
available-memory limits, nice 19 and idle I/O. It took 2.463 seconds;
peak sampled RSS was 2,000,601,088 bytes and minimum available memory
18,921,078,784 bytes. Direct guards, including stage-078 provider slots,
were stable. Outer session 5881 was separately observed to exit 0.

The direct historical `ModelCarrierSyntax.olean` provider is the independently
replayed stage-078 object, SHA-256
`9eaaefb9b4121df6d9c8f6f1c5feef1cc837fc38f51a831a005db072bdaaf900`.
No fresh-base objects were mixed into the search path. Historical package,
transitive and dynamic ancestry and sampled monitoring remain inherited
limits. This does not establish a 66-operation integer-leaf equation or
an internal rational-leaf sentence.

Attempt01 failed on the strong-factor multiplication order; attempt02's
global commutative simplification hit the deterministic heartbeat limit.
Both exact source/generator snapshots, logs, receipts and outer exits are
retained in `observations/attempt01` and `observations/attempt02`.

The successful output object is
`/tmp/normalized106-rational66-lean-priority-check03/Normalized106Rational66.olean`,
SHA-256 `6978d8ef65c4cb77311bd9028143b4c6af95847e103a966936694eedc6890299`.

| Artifact | SHA-256 |
| --- | --- |
| `Normalized106Rational66.lean` | `99b0d71b27771ed5416e295f28f6d1668a4c5a7cdbf8a756a7ac19b513129f42` |
| `build_lean.py` | `59976f3ec7825211ab45a0c72ab0224272a8b49f5a24a301a368e1f40c1f3a30` |
| `audit_rows.py` | `3a9ae46e45d075a020339835bcd9eab6d9d0ef95aa05befc0872a5ea75d8ecc0` |
| `row-audit.txt` | `2a7c64e0d30b30840e598315e7246e0b142905ef6d17b01fece65c47137cb3ee` |
| `check03.py` | `782495e146f6b69271b0c7878a2552af3c8c01442f0de045c788e3edc15cc820` |
| `observations/attempt03/compile.log` | `36548a4562d7b3a6bacacd89a2a50e273b9245866bdb25db5a5e487322614a74` |
| `observations/attempt03/result.json` | `6a172e130db1dac5c48afa6f0f9256231bfa9a23c3b748e5d7b0ee448922db42` |
| `observations/attempt03/outer-terminal.json` | `6d187c4da73a36eeff779373c9906bac9a593c35813baba548d0a12bc82b5a38` |
