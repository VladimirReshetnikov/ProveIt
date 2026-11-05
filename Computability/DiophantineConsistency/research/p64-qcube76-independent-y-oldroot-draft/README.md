# Unchecked actual-zero old-root guard

The signed auxiliary root in the 77 graph is `yold=V+e`; it can be negative
for an arbitrary positive input tuple. The intended theorem
`IndependentYOldRootDraft.old_root_ne_zero` states that it is nonzero at an
actual positive 77 zero. This is the guard needed before replacing it by a
positive absolute-value witness in the independent-`y` graph.

The draft's proposed chain is:

1. Use the existing same-valuation 77↔78 equivalence and 78 residual facts to
   obtain `W=0` and `Na=1` at the actual zero.
2. Transport those residuals to the P64 graph after lifting `Y=q³s`.
   Positivity gives `c≥3` and `i≥1`; `W=0` gives
   `A=Delta*(f²−1)=(i*c²)²≥2`.
3. If `V+e=0`, the auxiliary norm `Na=1` becomes `A*V²=1`. The existing
   discrete ordered-ring unit theorem forces `A=1` or `A=−1`, contradicting
   `A≥2`.

`IndependentYOldRootDraft.lean` sketches both a generic discrete-ring lemma
and its zero-specific graph application. **It has not been compiled.** In
particular, casts, rewrites through the lifted graph, auxiliary-carrier
identification and tactics may need correction; the imported independent-`y`
binding is itself unchecked. This packet is not a Lean theorem, an
absolute-value witness construction, a graph equivalence, or an iPRA endpoint.
No Lean process was run while the current-source rebuild occupies the slot.

[`check.py`](check.py) gives bounded integer sanity checks for the generic
nonzero implication and the strong-norm lower-bound pattern, including the
`A=1, V=±1` boundary where the generic exclusion would fail. The 19,899 and
3,120 tested cases are not a proof of the quantified model argument or an
actual graph-zero example. Reproduce them with:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/p64-qcube76-independent-y-oldroot-draft/check.py
```

| Artifact | SHA-256 |
| --- | --- |
| `IndependentYOldRootDraft.lean` | `e494d91733972c7d03f9d8b0860ca7779853ab4606aea4a556d20b724d6d12e2` |
| `check.py` | `246d7780de92b53465b02bdc77fb2df44a69134b82e21906e30f15036496cc30` |
| `result.json` | `a0d39420356050bf273313ea7c047559aa1f50e7259f126b7cf4741bb3568e29` |
