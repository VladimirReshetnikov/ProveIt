# Normalized seed to the exact ordinary graph factor

`ordinary_unit_of_normalized_seed` proves in an arbitrary `IΣ₁` model that
the actual free-J graph's ordinary factor represents `+1` from these equations
in that model's difference ring:

```
Q = Δ(f²−1),       d = c⁴,
n = Δi + (y−z),
f² = 1 + Δ(i c²)²,
(Δ i c²)² z² + y² = 1 + (Δ i c²)² y².
```

Here `Q,d,z,n` are the actual graph expressions selected by `parts`, evaluated
at the same valuation and ports. The multiplier for the graph's *ordinary*
strong equation is `Δi`, while `i` is the seed's *normalized* multiplier. The
proof constructs the tail witness `u=y−z`, derives `Q=d(Δi)²` and its
auxiliary equation, then applies the checked exact-graph tail theorem.

The theorem assumes the displayed same-valuation graph bindings and seed
equations. It does not construct seed elements, a graph valuation or the
`n` coordinate, establish positivity or coefficient binding, or produce an
iPRA proof. The difference-ring subtraction does not itself assert that the
corresponding natural coordinate exists or is positive.

The bounded author attempt 02 exited 0 in 3.109 seconds with no warning or
`sorryAx`. Source SHA-256 was
`5702767549b219dd28ef8eeed0ef0fd1f98b2dfd2538a4520f362305afd12efe`;
object `/tmp/free-j-normalized-tail-bridge-author-r1su8y8z/FreeJNormalizedTailBridge.olean`
had SHA-256
`ac0382cc1b23b7185e141cc0922ab24bd2f31df3ad76af30fba0d35ca4896298`.
The direct tail import, named transitive signed transport object and their
companions, and all 70 live selected coexistence-provider files were unchanged.
This is not an independent replay or a full audit of inherited provider,
package-transitive or dynamic ancestry. Lean reports `propext`,
`Classical.choice` and `Quot.sound` as metatheoretic dependencies.

Attempt 01 failed because the selected import did not provide the
`linear_combination` tactic. Its source and error are retained; attempt 02 used
a direct ring calculation without weakening the statement.
