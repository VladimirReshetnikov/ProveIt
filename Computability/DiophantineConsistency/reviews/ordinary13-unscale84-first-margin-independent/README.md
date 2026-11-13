# Independent source review: unscaling first-root margin

The source and receipt pins reproduce. This is a mathematical and source
interface review, not Lean elaboration, graph binding, a root witness or an
endpoint proof.

For natural tau, ell, k and s with the stated norm, `3s≤k` and `s≤ell`,
the signed-ring difference

```
tau²−(ell+s)² = 1+ell*(k−3s)+s*(ell−s)
```

is positive: all factors following the 1 are nonnegative. Both tau and
ell+s are nonnegative, so `ell+s<tau`. This remains valid at s=0 or ell=0;
no strict positivity assumption is used. The draft states precisely these
hypotheses and adapts the argument of the pinned **private** P73 `tau_gt`,
which cannot itself be imported as a public lemma. Tactics, model instances
and casts are untested.

For the specialization, setting ell=m*k turns the stated norm into the
general norm. Given s≤m and 8m+4≤k, k≥1 gives s≤m≤mk and
3s≤3m≤8m≤k. For the q³ specialization, q≥1 and Y=q³s give s≤Y, and
X≥1 and Y≥1 (the latter follows from s>0) give Y≤X*Y². Thus the
specializations supply the correct inequalities without assuming a desired
zero-map result. Actual graph extraction, large-k bound, port casts, and
binding the same natural root tau to the target witness remain separate.

The independent checker validates 19,125 bounded gap controls and 80 exact
q³ Pell instances, in addition to reproducing the author's symbolic check.
These finite tests do not establish the result in arbitrary models. No
concrete mathematical or premise mismatch was found.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-unscale84-first-margin-independent/check.py | cmp - reviews/ordinary13-unscale84-first-margin-independent/receipt.json
```
