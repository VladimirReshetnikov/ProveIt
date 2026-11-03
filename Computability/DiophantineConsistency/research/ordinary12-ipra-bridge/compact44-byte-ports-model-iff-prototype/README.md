# Model equivalence for the four decoded Lean byte recipes

`CompactBytePortsModelIff.shifted_model_iff` proves in Lean, in every
`ORingStructure` model of IΣ₁, that the following are equivalent:

1. Some model-natural 12-vector is an internal zero of
   `positiveShift (retainedExpression byteP)`.
2. The encoded 215-state machine halts internally in that model.

Here `retainedExpression` is the separately checked generated 95-gate
**Lean** expression, `positiveShift` substitutes `x+1`, and `byteP` decodes
each of the four closed **Lean** byte recipes in `ℕ` before casting to `ℤ`.
`byteP_eq` uses the checked four-port decoding theorem to identify these
integer constants with the exact symbolic tuple `[beta, K, MC, beta+high]`;
the fourth component has one beta shift. The zero and halt witnesses are
internal to each model and may be nonstandard.

This is an all-model theorem, **not yet a Lean proof that an iPRA derivation
exists**. The four recipe-to-parent-payload comparisons, gzip decoding and
the 95-row JSON-to-generated-source check are external provenance rather
than Lean file theorems. Parent-to-supplement correspondence and any PDF
transcription remain separate. This is not a claim about the 14-variable
`equation.pdf`.

The guarded preflight inventories 10,751 recorded model-provider files and
compares every selected artifact path with the four-byte provider; it creates
a fresh 1,286-file union. All 9,981 overlap occurrences matched hashes,
with no suppressed foreign companions. The bounded mixed-provider author
run `observations/attempt03` exited 0 in 2.130 seconds without warnings or
`sorryAx`. The selected union, all recorded model-provider paths, earlier
byte-provider records, producer source/object hashes and direct dependency/
companion guards remained unchanged at the recorded checks. Exact source,
dependency listing, log and terminal receipt are retained. Source SHA-256:
`c6e81cf3ad13e70e55f68a8ab97702815fc78ef025facc06c2143ccecbc61932`;
object SHA-256:
`6feb5a290fa5d15e5f9b539fcd3a5ce7e233e3783cc0115ed6dde63b42515e6a`.
Lean reports `[propext, Classical.choice, Quot.sound]` for the named
theorems as metatheory dependencies, not iPRA axioms.

The first runner stopped before Lean because it incorrectly expected a
`run` field in the byte-tuple receipt; its exact runner and traceback are
retained in `observations/runner-attempt00`. The first Lean attempt, kept
in `observations/attempt02`, failed because `Nat.ofDigits` is semiring-
polymorphic: the initial type annotation selected integer decoding instead
of casting a natural decode. Attempt03 explicitly annotates the decoded
value as `ℕ` before the cast. Error-recovery `sorryAx` output from the
failed attempt is not proof evidence.

This is a single exploratory author-side mixed-provider build, not a paired
replay or a full symbolic/project/package/dynamic ancestry audit; all
filesystem checks are point-in-time. The selected-provider and overlap
manifest is retained under `observations/prepare-attempt01`.
