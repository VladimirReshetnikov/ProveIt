# Fact-level early index for the actual residue root

This source-only wrapper proposes the early Pell index and congruence from an
explicit **natural norm for the actual residue-adjusted first root**. It does
not assume any equality to the original free-J `core.z`, but neither its source
nor its imported providers have been elaborated for this client.

For model naturals `q,X,Y,k,R,tau,s`, the hypotheses are `q,X,Y>0`,
`Y=q³*s`, the explicit first norm for `Q=X*Y²`, the rank window
`24≤R` and `R+q³+q+1≤q⁴`, and the actual main-root congruence cut
`q⁴ ∣ magnitude (R+1,k)`. It proposes a model-natural n and w satisfying

```
13≤n≤k,  xcoord n B=tau,  2*ycoord n B=k,
(2*n)%q⁴=R+1,  R+1≤2*n,  R+1≤k,  k=2*n+4*Q*w,
B=2*(Q-1)+1.
```

The source calls the existing `positive_parameter_solution`, then applies
`residue_quotients` separately modulo `q⁴` and `2Q`. This is an **early
congruence**, not an assertion that `2*n=R+1`. The actual graph-to-natural norm,
main-root rank divisibility, positive-C/rank window, compact port casts,
all source/provider dependencies and Lean elaboration remain open. Later
exact-index, projection, physical equation and internal iPRA endpoint
obligations are not supplied by this wrapper.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-residue-first-index-model-draft/check.py | cmp - research/ordinary13-residue-first-index-model-draft/receipt.json
```

The read-only checker pins relevant source bytes, reruns the independent
interface audit, and checks a finite recurrence family. It does not execute
Lean, stage artifacts, validate nonstandard-model proofs or authenticate
compiled providers.
