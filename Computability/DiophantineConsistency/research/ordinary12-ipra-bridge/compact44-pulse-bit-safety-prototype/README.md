# Compact44 dummy pulse: bit and packed-cell safety

In every model of IΣ₁, `CompactPulseBitSafety.pulse_preserves_noCarry`
proves the generic fact that adding `2^k` to `x` preserves binary no-carry
against `m` if `x` and `m` already have no carry and **both** have zero at
bit `k`. The proof handles all model positions by splitting each number into
low and high binary parts and checking the least significant high bit.

The symbolic compact44 low mask has bit `67*1063` clear, proved from its
actual finite-list recipe without expanding the large numeral. The specialized
`compact_pulse_noCarry` therefore requires only that the baseline cell have
zero in that bit and already have no carry against the symbolic mask.

`CompactPulsePackedCell` connects this to the represented construction:

* For every model row `a`, `packedCell a 0` has the dummy bit clear.
* If this particular cell has no carry against the symbolic low mask, it
  still has no carry after adding `2^(67*1063)`.
* For any Σ₁-definable row function, any model length `N`, and any `j<N`,
  the corresponding dummy bit is clear in the outer represented block sum
  of normalized cells with zero dummy input. This also holds for nonstandard
  model lengths.

These results **do not prove the baseline no-carry assumption**. They also do
not prove the outer word has the correct transition rows, or establish the
remaining product, block, high-mask, graph-zero, or iPRA-proof obligations.
The finite-list symbolic mask's identification with a particular retained
compressed literal remains subject to the separate existing binding audit.

The first generic check (session 24980) exited 1; its compiler log is saved,
but that exploratory invocation did not retain a source snapshot or direct
dependency guard. Guarded attempts 02–04 also exited 1; their failed sources,
dependency scans, logs and receipts are retained. The guarded generic attempt
05 (session 86517) exited 0. Packed-client attempt 01 failed for a missing
constant-function definability instance; the corrected guarded attempt 02
(session 70109) exited 0. Both successful runs had unchanged sampled direct
object/companion guards, no warnings, and no `sorryAx`; their named theorem
reports list only `propext`, `Classical.choice`, and `Quot.sound`. They are
single-author incremental builds with inherited provider, package,
transitive and dynamic-loading ancestry; no paired replay or independently
authenticated complete closure is claimed. The retained runners refer to
the recorded `/tmp` providers, which may be ephemeral.
