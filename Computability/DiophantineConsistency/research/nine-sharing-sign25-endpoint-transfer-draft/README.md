# Direct standard-theory transfer retry

The preceding standard wrapper applied the reverse direction of
`IPRAStandardTheory.provable_iff`. Its proof is defined in terms of the more
general `IPRAStandardTheory.transfer` applied to `native_axiom`. This
source-only retry applies that transfer directly, avoiding elaboration of the
intermediate `Iff` projection. The source retains the same local opacity
settings and same partial native provider. The translated wrapper is unchanged.
The exact cause of the previous interpreter exception is unknown; this change
may not avoid it. No standard or translated theorem is claimed before a bounded
Lean run and independent audit.
