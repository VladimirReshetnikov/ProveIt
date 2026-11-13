# Positive reverse carrier coordinate under explicit quotients

`TenPositiveReverseCarrier.positive_carrier` is a generic model lemma. Given
natural data with `Kpos=H*κ`, positive τ,y and `κ<f`, it constructs positive
n satisfying

    n+κ = τ*f*y + u²*(b*t) + t + ρ,

and proves the displayed signed carrier identity
`Z = (b*μ²*H)*(τ*f*y)` for `Bt=b*t` and `e=μ²*ρ`. The natural n is made
positive by the strict bound on f; no subtraction is assumed to stay positive.
This is conditional algebra: it does not independently supply the κ,ρ,
transport or Pell hypotheses, identify the actual 80 graph evaluation, prove
a graph zero, or establish an iPRA endpoint.

Accepted guarded check `observations/carrier-attempt03/` produced
`/tmp/reverse-carrier-fr1w8a_6/ReverseCarrier.olean`, SHA-256
`614ce881139dbf86b9080fa156e87f2c84d0b19eceabc522b008f44b8c9ebbaa`.
The first two failed attempts record a missing framework import and a
natural-cast elaboration issue. All direct imports are resolved and checked
against explicit ordered LEAN_PATH paths and hashes before/after Lean; broader
transitive source-object, project/package and dynamic limits are inherited.
