# Latest main review for phase18

Pinned main `f0ae4e0991ca44a7bb4e5671d42e33d775e48035` was fetched by exact object
ID with `--no-write-fetch-head`; no refs or working files changed. Relative to
`140d832128fd43873f16e385766cd3cee08df8a9`, its only maintained Lean change is
Claude's `733e83e049adf1bb8c5e8d8ba76927b138cf452c`: nine proof-only files,
**155 fewer lines / 2,236 fewer bytes**. All nine files still match their 140d
versions in our published phase17 HEAD `7a1273555ba3c2d4f6db087567309f692660ec72`.
Before/after snapshots, `lean.diff`, `changed-paths.json`, `commit-messages.txt`
and `review.json` preserve the exact selection. All nine diffs were fully read;
157 declaration heads match after comment stripping and whitespace normalization.
Imports, public statements, data and definitions remain unchanged.

The ideas are useful and compatible with the current work: anonymous constructor
and match-function proof terms; `Exists.imp` for repacking witnesses;
`forall_congr'`/`exists_congr` for mirrored quantified cases; grouped identical
formula constructors; direct application of the existing matrix-instance theorem;
and inlining actual single-use local facts. `orderedPair_injective` reuses its
union equality before destructuring the second pair, removing a reconstructed
proof. `RegisterPath.read_writeRegisters` merges the common induction/case script;
finite execution soundness merges the four reflexive cases. The correction to
its commit-message snippet is recorded in `7bfe6499e2`.

The six 222/254 macro files and `generate_l2k222.py` are byte-identical in 140d,
f0 and current phase17. There is **no path overlap** with the concrete four-file
macro-sharing proposal under `/tmp/k215-next-macro-sharing`. The other formal
commits after140d (`7bfe6499e2`, `d47476021e`) alter only the Rocq branch. The
latter removes an unused s0-based enumerator interface because the actual route
starts from the bootstrap seed. That caller-census principle is relevant to future
Lean cleanup, but no Coq work is required or performed here. Other new commits
catalogue Diophantine manuscripts and do not change this selected Lean closure.

I recommend combining the nine Lean edits with the 509-line macro proposal, after
reviewing and checking the new macro interface and finite closed-set obligation
first. The changes give a static total reduction of **664 Lean lines / 26,606 bytes**;
retiring the 74-line producer raises that to 738 maintained lines / 30,412 bytes.
This combines Claude's completed proof editing with our distinct structural work.
The macro proposal still enlarges the standalone215 endpoint from 174 to 178
modules; combined source size is estimated at 1,768,097 bytes. This is a reduction
of maintained duplication, not a smaller endpoint closure.

Using phase17's exact 213-provider import graph, the main-only changes force 93
providers, including all nine expensive site batches. The macro-only changes
force 19 providers and no site batch. Their union forces 106 providers and all nine
site batches. Summed last recorded provider durations are about 1,772s, 45s and
1,814s respectively; these are planning estimates, not new timing measurements.
A combined check therefore handles both useful simplifications with only about 42s
of additional historical compilation cost beyond checking main alone. Separate
checkpoints would retain six overlapping provider recompilations and split the
accepted source state. The final combined source/import map must be recomputed
once candidates are frozen, including the new typed macro API client and audits.

Claude's commit reports serial `lake build` of the nine edited modules, a green
37-module rebuild of the KEndpoint closure and eight named side importers.
The commit does not carry the exact source/object/toolchain/command ledger required
for our portable acceptance. No current Claude worktree is registered locally;
the registered main checkout remains at 68ce65f18e. These build claims are attributed
context, not reusable objects or acceptance of our 213-provider selection. A fresh
combined source-transitive check and exact endpoint/API profile review remain due.
No compiler, generator, supplied checker, or other agent's worktree was executed
or modified during this review.
