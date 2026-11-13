# Matched field digits at the concrete compact positions

`CompactWordFieldDigits.lean` connects compact tile-color matching to the
actual packed-word digits in every IΣ₁ model. For any definable row and dummy
functions and any in-range adjacent rows of a `CompactWord`:

* for each `u < 9`, the current row's digit at phase `983+u` equals the
  vertical predecessor's digit at `1013+u`;
* for each `u < 8`, the current row's digit at `1003+u` equals the
  horizontal predecessor's digit at `1023+u`.

The proof checks the exact 41-slot lookup for these finite ranges and uses the
separately checked model-uniform payload-bit consequences of tile-color
matching. Dummy values are normalized by the underlying word construction;
they require no additional Boolean assumption in this statement. These are
source-digit equalities only: identifying the raw stencil/physical block
columns, proving their parity, handling marker phases, high-mask no-carry,
graph zero and an iPRA proof remain separate tasks.

The first bounded author attempt failed on dependent finite-index elaboration
and cast-normalization errors and emitted unused-simp warnings; its source
and full compiler log are retained, and none of its failed reports is
accepted. The corrected attempt, session `5551`, exited 0 with no warnings or
`sorryAx`, unchanged sampled direct dependency and companion guards, and the
expected named axiom reports containing `propext`, `Classical.choice` and
`Quot.sound`. Its command, source/object hashes, dependency scan and log are
retained. Provider package, transitive, dynamic and between-observation
ancestry is inherited; `/tmp` paths are ephemeral. No paired replay or full
closure audit is claimed.
