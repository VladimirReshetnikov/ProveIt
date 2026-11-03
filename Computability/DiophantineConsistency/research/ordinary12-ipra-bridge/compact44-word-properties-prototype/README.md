# Global properties of the constructed compact word

For arbitrary Σ₁-definable model functions `row` and `dummy`, Lean proves
that `packedWord row dummy N` is Σ₁-definable as a function of `N`, and that
all its radix-`2^67` digits at positions below `8807*N` are at most one. If
`row` satisfies the existing `CompactWord row N s` structure, its marked
origin and positive length imply the packed word is at least one. The origin
result applies to any dummy function, since selector position zero is
independent of the dummy input.

The guarded single-author compile exited 0 with unchanged sampled direct
object/companion guards, no warnings or `sorryAx`, and only `propext`,
`Classical.choice`, and `Quot.sound` in the three named axiom reports. The
runner and observed compiler/dependency records are retained under
`observations/attempt01/`; their `/tmp` provider paths may be ephemeral.
Provider transitive, package, dynamic-loading, and between-observation
ancestry is inherited. The result does not construct a `CompactWord` from a
halt, prove low- or high-mask/product conditions, produce a graph zero, or
establish an iPRA endpoint.
