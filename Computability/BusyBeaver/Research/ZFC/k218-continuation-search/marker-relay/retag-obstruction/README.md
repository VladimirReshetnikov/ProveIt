# The guarded CC2 loops cannot be retagged to CC3

The first [relay runtime counterexample](../evidence/runtime-attempt/literal-counterexample.json)
at source ordinal4569 cannot be repaired by an ordered tree reassociation
that changes its `CC2` to `CC3` while preserving the exact ordinal CFG.
A `CC k` returning from ordinal i to r needs k disjoint nonempty left-sibling
intervals between them. Here i−r=2, so k≤2.

The [ordinary proof](proof.md) extends this observation to all nine
`(CD6,CC2)` occurrences in the accepted primary218 source. Five have this
distance-two obstruction; in the other four, the preceding `CD5/CC1` loop
is forced to remain a subtree, again allowing only two right crossings.
Both decrement branches and continuation targets are preserved in this
claim. Source141's valid four-increment retagging has different premises.

The [literal census](source-review.json) and [original reader](original-census.py)
were authored by `review_upstream_reflection`. The reader verifies the nine
source contexts and successors; the all-tree counting argument is ordinary
mathematics, not a proof-assistant result. There was no search or binary
runtime rerun. This excludes the specific CC2-to-CC3 reassociation route;
it does not exclude a different comparison word, a physical repair, or a
new allocation. No state saving follows from this packet.

The [portable reader](census.py) has only the path changes shown in
[portability.diff](portability.diff). Its first [fresh reproduction](portable-check.json)
passed. To repeat the inexpensive source census from the repository root:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k218-continuation-search/marker-relay/retag-obstruction/census.py --repo . --output /tmp/k217-retag-census-new
```

The output directory must be new. The original Source141 manuscript pin
is retained in the historical source-review record; reproducing this
census requires only the maintained source and relay counterexample.
[publication.json](publication.json) records the exact original files.
