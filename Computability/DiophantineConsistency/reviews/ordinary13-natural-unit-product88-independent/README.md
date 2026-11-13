# Independent review: 13-natural-input, 88-operation graph

The [candidate](../../research/ordinary13-natural-unit-product88/README.md) has the stated external natural-zero equivalence with the 89-operation parent under `beta>0` and `K0>=0`, conditional on the reviewed parent unit-factor exclusions. Its relation to the earlier positive-parent graph also inherits the independently reviewed 89-operation root switch. This is not a Lean or iPRA theorem, physical PDF binding, fresh provider replay, or minimality claim.

The independent receipt verifies that the new graph is exactly the old 89-row graph with the `J=n_J+1` gate removed and its two consumers redirected to `n_J`. Consequently the new graph at `J` equals the old graph at `n_J=J−1` over arbitrary integer inputs and ports. The receipt checks all remaining rows, the graph's topology and liveness, and the particular first-factor rows used below. It independently reauthenticates P72 bytes against P115 hashes and computes the degree-99 diagonal ray modulo 1,000,000,007. The degree upper bound is inherited under affine substitution from the reviewed 89-operation graph; this receipt does not independently rederive that bound.

For a new natural zero, the parent's all-integer factor exclusions force the first factor to equal one. If `J=0`, then `b=0`, `q=1`, and `X=w>=1`. The retained shifts give `F>=1` and `alpha>=1`, so `C=1−F−alpha<0`. With `K0>=0`, `B=C*(X+K0)−F<0`, hence `Z=−B>0`. But the first factor equation says `Z²=b²*(1+ell*(ell+k))=0`, impossible. Thus `J>0`, so subtracting one gives the old natural valuation; the reverse map increments its `n_J` input. The local exclusion uses `K0>=0`: a small `K0<0` assignment in the receipt makes `B=0`, although it is not asserted to be a zero of the full graph. The `beta>0` assumption is inherited when composing with the 89-to-positive-parent equivalence.

The finite controls do not prove the unbounded positivity argument or the inherited endpoint. In particular, no internal iPRA proof or coefficient-to-document binding follows from this review.

Run from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary13-natural-unit-product88-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary13-natural-unit-product88-independent/result.json
```
