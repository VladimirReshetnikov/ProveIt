# Independent direct symbolic-K closure review

The source-only review passes for closure-plan commit `d887612e55`.
Independent no-Lean session 9032 exited 0; its `CHECK.json` records the
seven source/import chains, 143 matching provider objects per side, 60
external direct companion slots, 140 empty target slots, ten Init slots, and
all 17 exact declaration names and individual axiom sets. The review reran
the pinned source scan and independently rejected optimized execution; its
own optimized invocation also exited 1. It verified the seven current source
hashes against their stated Git commits and checked same-side topological
availability. The parent audit receipt and observed exit were pinned and
checked, but the full parent audit was **not** rerun in this review.

The source plan lists 17 reports with different axiom sets. The review checked
the exact source `#print` names against all seven retained author-only logs
and their committed hashes; the resulting name/set table is in `CHECK.json`.
The author-only runner session 60092 recorded exit 0, but inspecting those
logs is not a paired rebuild or an independent artifact audit.

The graph client defines a new symbolic `directK = paramKernel rho` and
assumes a positive zero for the graph using that symbolic term. Neither the
source closure nor the observed author run proves `directK` equals the
retained K bytes, a displayed coefficient, or the complete retained tuple;
the earlier `kernelNat = paramKernel rho` proof attempt remains unproved.
No decoder, machine correctness, construction direction or internal iPRA
result follows. Input hashes and companion states are point-in-time checks;
package/transitive/dynamic ancestry and sampled-resource limitations remain.
