# Independent review: eta-natural direct projection

The proposed fact-level client matches the pinned `direct_projection` and
`projection_quotient` source interfaces. Its exact carrier rearrangement and
range inequalities are mathematically consistent under the displayed
premises. No source-level witness mismatch was found. This review does not
elaborate Lean, build providers, extract a graph zero, or establish an iPRA
endpoint.

The theorem assumes one natural `main` in the oriented carrier and explicitly
requires `xcoord R (Y*(X+1))=main` and
`ycoord R (Y*(X+1))=c` for the same `R` and base. The same `w` appears in
`k=R+1+4*X*Y²*w` and `W=4*X*q*s*w`, and the same `s` appears in
`Y=q³*s` and W. The statement does not itself construct any of those
witnesses, identify them with witnesses from another graph theorem, or assume
a first Pell index `n`; such alignment must be supplied by a later client.

With `U=Y*q²` and `Y=q³*s`, the stated identity
`4*X*Y²*w=U*W` follows by commutative-ring algebra. Substituting it and the
exact k equation converts the assumed no-`E*q` carrier to the **same**
root-balance orientation required by `DirectMainProjection.direct_projection`.
That imported source requires `U>0`, `H>0`, `X<H`, and `P<H`; its
cancellation is by the explicit positive `U`, not by a hypothesized divisor
of X. For positive q and s, `Y>0` and `U>0`. For natural X, `a=Y*(X+1)`
gives `X<a`, `Y≤a`, and `a<H=3+4a`. Thus the separately assumed strict
`2^R<Y` gives `2^R<H`. No unspoken strict growth or positivity assumption
is needed for these displayed implications.

The pinned `projection_quotient` source quantifies over arbitrary model
naturals `a,R` and uses `IΣ₁` induction to produce `t` in
`xcoord R a=2^R+a*ycoord R a+(4a+3)*t`. The two supplied coordinate
identities give exactly the projection premise with `P=2^R` and the same
`main,c`. The client then applies the matching direct-projection argument.
The derivation of `2^R<Y` itself, the actual oriented root and shared
coordinates, factor-unit and norm extraction, fixed compact ports, provider
closure, zero maps, and all Lean proof/axiom checks remain separate.

The prototype graph is a pinned structural experiment. Its `Dstar` matches
the no-`E*q` form under 250 bounded evaluations; these checks are not a
model-level evaluation theorem. A separate 300 controls check the balance
identity and applicable bounds, and 135 check standard Pell projection
instances. They do not prove the imported theorems for nonstandard models or
validate the unelaborated source.

From this directory reproduce the independent receipt with

```
python3 -I -S -B check.py > /tmp/eta-zero-projection-independent.json
cmp result.json /tmp/eta-zero-projection-independent.json
```
