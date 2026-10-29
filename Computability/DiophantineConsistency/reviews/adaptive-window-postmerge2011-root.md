# Window replay after the CarrierRadix refactor

Two isolated builds rebuilt the changed `ArithmeticCarrierRadix2011` and its
window suffix through the actual-zero client and checks. All five source,
object and complete-log hashes match. The drivers verify that this was the
only changed source among the prior 25-module window refresh, and use the
independently replayed prior window provider for unchanged objects. The
[independent driver, snapshots, state and provider inventory](adaptive-window-postmerge2011-root-replay/)
and [author evidence](adaptive-window-postmerge2011-author.md) are retained.

A subsequent upstream merge changed `ArithmeticBinomLegendre.lean` in the
inherited population chain. Thus this receipt records the intermediate
post-radix/pre-Legendre source snapshot, not a complete current-source
window replay. Foundation, packages and unchanged upstream objects remain
inherited cache boundaries.
