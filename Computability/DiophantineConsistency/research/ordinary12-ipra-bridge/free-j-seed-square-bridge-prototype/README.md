# Outer seed squares and the exact free-J carriers

`carrier_units_of_seed_squares` proves in any `IΣ₁` model that both exact
free-J carrier factors represent `+1` when the following difference-ring
equations hold at the same graph valuation:

```
Z = M*τ,             Dstar = U*χ,
τ² = 1+(X*Y²)*(X*Y²+1)*k²,
χ² = 1+(a+1)*(a+3)*c².
```

`X,Y,η,ζ` are the actual graph coordinates 5, 6, 8, 9, `k=η+ζ`, and the
remaining symbols are actual graph expressions with `M=q³(q−1)`. The proof
checks the graph's exact first norm expression by reflexivity and uses ring
identities to match both norm squares before invoking the checked carrier
witness theorem. Thus the two square equations have the shape supplied by the
outer Pell seed; they are still assumed here, including their interpretation
in the model difference ring.

This theorem does not construct a graph valuation or seed witnesses, nor does
it derive either `Z=Mτ` (transport) or `Dstar=Uχ` (adaptive lift). It does not
establish graph-coordinate positivity, the ordinary third factor, fixed-port
calibration, or an iPRA proof.

The bounded author attempt 01 exited 0 in 3.064 seconds with no warning or
`sorryAx`. Source SHA-256 was
`c7917cc866bcf6e6389308065f98ff7001d30a8c84e9109d3a114ec3f467dab4`;
object `/tmp/free-j-seed-square-bridge-author-8jgp6z_s/FreeJSeedSquareBridge.olean`
had SHA-256
`1abb078c8978dddd5f43a50fc9e78249f608aa26d2e941040c79b5647ca75d3e`.
The runner checked that all 70 overlapping live provider paths matched and
guarded all 167 provider files plus direct and named transitive bridge
companions. This was a single-author check, not an independent replay or an
audit of inherited package-transitive and dynamic ancestry. Lean reports
`propext`, `Classical.choice` and `Quot.sound` as metatheoretic dependencies.
