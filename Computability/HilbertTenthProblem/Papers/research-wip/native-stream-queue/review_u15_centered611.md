# Independent review of the centered 611-operation U15 compiler

**PASS: both complete polynomials are identical to the reviewed621 parent.** The ordinary circuit costs611=239M+372A, with102 positive witnesses and46 comparisons; the raw circuit costs368=131M+237A, with51 witnesses and11 comparisons. All gates, including centered offsets and the larger state comparison, are paid. This reduces one direct binary-tape construction and leaves the overall87-operation bound unchanged.

The full [source](u15_packed_centered_states611.py), companion proof and emitted circuits were read. Source SHA256 is `3208cefa385789f2a7774bd348316a99e57f841154c40eed065e159bad4d20ce`; the parent pin is `8cadeb24c695b1956cd5cb25f93d41261065ddc45c116d7c9b0d0e3d7e4906d3`. The [independent checker](review_u15_centered611.py) and [receipt](review_u15_centered611.json) authenticate both files and independently execute the complete arithmetic.

The review expands every relevant affine register into29 edge-hat coefficients plus a constant. It verifies exact equality of J,S,Dir,W,WD and the identities `Qdev=Q-7J`, `Ndev=N-7J`, including all hat offsets. The actual state comparison in the parent is extracted from its emitted source, rather than assumed from its description. The two actual residuals are

    old: B*N-Q-P
    new: B*Ndev-Qdev+6P-7.

Both sources' actual P registers expand to `(B-1)J+1`. Substituting the two proved affine identities makes the residuals equal as polynomials on every supplied tuple. This computed P identity holds away from zeros; it is not a semantic constraint borrowed from the solution set. Signed deviations are computed intermediate values, not new positive witnesses. Current metadata correctly exposes Qdev/Ndev instead of misleading Q/N names.

Exact structural interning then verifies55 remaining comparison-pair DAGs across the two interfaces and58 common semantic/tag/truth DAGs. Each complete sum-of-squares finalizer is independently reconstructed literally. Equality of every residual therefore proves equality of the complete polynomial, over integers and also over reals. Independent gate closure, liveness, formal-degree propagation and operation ledgers pass for both parent and child. The saving is13 multiplications offset by3 additional additions/subtractions, net10 operations.

The [separate exact-degree1936 certificate](u15_packed_exact_degree1936.md) proves the exact degree of the646 ancestor. The621 and611 all-value polynomial identities transfer that exact degree to both new interfaces and every fixed valid program slice. Frozen compiler metadata and its own receipt continue to report their propagated upper bound only. This is an inherited exact-degree conclusion, not a new lower-degree construction.

Finite supplemental checks independently evaluate96 complete integer SOS assignments, including48 signed cases and2,736 residual comparisons, and eight rational assignments. They reject1,331 malformed public calls, check six nested defensive-copy boundaries and two cold import-isolation cases. Public parent/build/source accessors copy their results; canonical mutable holders are private. Flags and coefficients require exact scalar/container types. Source pins are rechecked on public access. The compiler rejects optimized Python before assertion-based inherited constructors can execute.

The author's default read-only receipt replay also passes:128 complete output identities,64 signed cases,3,648 residual comparisons,1,153 malformed rejections, six defensive-copy checks and two cold import checks. These are finite checks supplementing the exact identities. No huge native Pell witness is materialized, and no stronger loader or universality theorem is inferred from the sampling.

From this directory, reproduce the independent review with:

```sh
python review_u15_centered611.py \
  --source u15_packed_centered_states611.py --root . \
  --output /tmp/review_u15_centered611_replay.json
```

The output should equal the saved receipt. SymPy is used only for the small exact state-residual identity. Both sources retain the paid ordinary input, native range/controller predicates, fixed-arity unbounded duration and inherited valid-program conventions.
