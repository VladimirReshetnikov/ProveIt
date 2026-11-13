# Initial MC boundary-window checks

The bounded author check of `CompactLowByteBoundary02.windows` passed for
the eight indices `[7890,7898)`. It states that each indexed value of the
closed Lean byte recipe equals the corresponding symbolic MC window. The
checked source SHA-256 is
`371fe0cee8a97e3350b8124c48b32512315fc10c2393280af7800a46b5dfe639`;
the resulting object SHA-256 is
`740314fcbf396cd36c0a78d261c4df864190bbd9b7a37d438c0383934ac2620f`.
The compiler exited 0 in 7.705 seconds without warnings or `sorryAx`;
recorded direct dependency/companion guards and the generic byte-window
provider were unchanged. The theorem's Lean metatheory axiom report is
`[propext, Classical.choice, Quot.sound]`, not a list of iPRA axioms.

The preceding `CompactLowByteBoundary01` compiler invocation returned 0
and produced an object, but emitted an `unnecessarySeqFocus` linter warning
because its interval has one case. The runner therefore **rejected** the
attempt. Its exact source, log and receipt are retained here; no accepted
boundary-01 result is claimed. A corrected single-case source must be
checked separately before use in the complete assembly.

Both checks use the generated closed byte recipe and inherited symbolic
providers. This packet is an author-side observation, not a paired replay,
full transitive/package/dynamic ancestry audit or file/gzip binding. The
remaining boundary modules and global 73,759-byte reconstruction are open;
external parent-payload and supplement provenance, a PDF and iPRA remain
separate. Checks are point-in-time.
