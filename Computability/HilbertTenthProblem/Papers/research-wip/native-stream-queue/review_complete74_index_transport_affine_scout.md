# Independent review: retained-index/quotient affine complete74 scout

**PASS; no requested author change.** I read the frozen [source](complete74_index_transport_affine_scout.py), [receipt](complete74_index_transport_affine_scout.json), and [proof/scope note](complete74_index_transport_affine_scout.md), together with the actual complete74 sources and relevant signed-projection and compiler mask restrictions. The author pins are:

| Artifact | SHA256 |
|---|---|
| Source | `21577acbd2c331b3f0a71b7d680e80384bbc0fb87a71a7691532fe53bc6fb213` |
| Receipt | `7f1ee37c769911c8f085a0fd03832b9d91b3315e944818832f237597aca92dd4` |
| Note | `26de3b12bcbf0d28cc9810c6af4c058db5c2c5db2f6f99c85bbfb2679e5b53b8` |

The [independent helper](review_complete74_index_transport_affine_scout.py) imports neither the author nor any historical compiler. Its [receipt](review_complete74_index_transport_affine_scout.json) includes its own source hash and all eight author/parent pins. It independently reconstructs every declared recipe from the pinned parent gate lists and compares every census hash and ledger, plus all fifteen saved complete sources, comparisons, interfaces and finalizers.

## Actual finite scope and costs

There are exactly `3*3^4=243` recipes: the three actual raw30/positive22/signed20 sources, with shifts `-1,0,1` independently on supplied `r,j,h,zquot`. Every nonzero shift pays its old-coordinate restoration. The only special source rewrites are the documented `r+1` cancellation and `j+1` redistribution; this is not all affine arithmetic or all possible evaluation schedules.

I independently obtain, in each mode,

\[
 74+[s_r=-1]+[s_j=-1]+[s_h\ne0]+[s_z\ne0],
\]

with40 multiplications and histogram74:4,75:20,76:33,77:20,78:4. All gates and supplied ports are live. The finalizer independently adds `e` differences, `e` squares and `e-1` sums, so the minima remain130/106/100 for19/11/9 equations. No new universal bound or general lower bound follows.

The independent enumeration covers all243 recipes, not just the fifteen saved sources. Its total is27,702 paid live polynomial gates. The twelve minima alone claim positive-zero bijections; the other231 recipes correctly claim only all-value polynomial pullbacks. They are not labelled unsound.

## Full polynomial transfer

All consumers matter. In particular the retained `r` appears in the index addition, the auxiliary norm argument and the packing comparison. Supplying `r+1` deletes the old `+1` but requires a paid restoring subtraction at its other consumers, so it ties. Supplying `j+1` keeps

\[
 H=(j_{new}c-r)-c
\]

in the auxiliary norm, while the linear residual becomes `(j_new*c-r)-of`. Deleting `of-c` pays for the extra subtraction in the norm argument. Omitting that restoration would change the norm and is not among the audited schedules.

I independently expand these two local identities in unrestricted atoms `j,c,r,of`. The remaining source is the literal generic coordinate translation. Combining the checked local replacements with that unchanged translated graph proves every full residual and the complete SOS identity. The independent helper checks exact regenerated sources and private consumer sets; it does not merely call the author's symbolic verifier. Supplemental exact evaluations cover486 complete outputs,243 rational cases and6,318 residual values.

The three uniform exact degrees52/84/84 transfer because invertible constant translations preserve the highest homogeneous part. The propagated bounds52/100/100 remain correctly distinguished from those exact degrees. Fixed program numerals keep degree zero and their inherited compiler restrictions. The raw independent k and projected `eta+zeta` ports are preserved.

## Positive inverse without circular native recovery

For the twelve minima, old coordinates are initially positive except that `r_old=r_new-1` and/or `j_old=j_new-1` might be zero. No full parent theorem is used to exclude those boundaries.

With the actual shifted source MF convention and `q=(B-1)J+1`, the packing mask minus `q²-1` is exactly

\[
 T'=(MCJ+1)+q(MF_{native}J-1).
\]

The actual fixed compiler restrictions `B>=16`, `0<MC,MF_native<B-1`, `MC>=2`, `MF_native>=4`, and `J>0` give `0<T'<q²-1`. Every other packing term is a multiple of `q²-1`. Thus the retained packing equality excludes `r_old=0`, without assuming q dyadic, an accepted history, or positivity of a signed intermediate. This argument applies to all three source modes.

For the quotient, the actual retained ratio comparison/definition gives `c=kY+eta>1`. Write `A0=a+2`, with `a>0`. The actual main norm is

\[
 d²-(A0²-1)c²=1.
\]

If `1<c<2A0`, then its right-side value for `d²` lies strictly between the consecutive squares `(A0*c-1)²` and `(A0*c)²`. Consequently `c>=2A0`. This uses no Pell-index classification or positivity of j. The retained strong equality implies

\[
 f²=1+i²c^4/(A0²-1)>c^4/A0²,
 \qquad f>c²/A0\ge2c.
\]

Since `o>=1`, it follows that `of-c>0`. The restored linear auxiliary equality `j_old*c-r_old=of-c` now forces `j_old>0`. In raw30 the required native quantities are positive supplied coordinates with their retained equalities; in both projected forms c,a and the main root are explicitly positive computed expressions. The signed20 input-root/marked-word restoration is not assumed in this argument.

Only after these boundary exclusions are all old supplied coordinates positive, permitting the parent theorem. The forward maps add0 or1 and are positive directly. The two maps are inverse translations on full positive zeros. The independent finite checks of672 actual pretyping mask combinations and1,560 consecutive-square cases supplement these elementary proofs; they are not their justification.

The mask-only obstruction is also correctly narrow: on the repunit slice, the packed index and any fixed-mask change are divisible by J. For `J>1`, such a change cannot implement a unit translation. This does not exclude a different history protocol or an additional paid transformation.

## Replay and limitations

```sh
python /path/review_complete74_index_transport_affine_scout.py \
  --root /path/to/native-stream-queue --author-root /path/to/author-trio \
  --expect /path/review_complete74_index_transport_affine_scout.json
```

The independent writer and fresh exact replay from `/` pass. The review proves source transfer through independently reconstructed rewrites and local coefficient identities; it does not expand the huge full multivariate polynomial into monomials. No accepting Pell tower is numerically materialized. No historical large suite, generic hostile-API audit, repository edit or Git mutation was performed. The finite no-improvement result and its twelve valid positive-coordinate ties are accurately separated from universal optimality claims.
