# Model-internal divisible Pell ordinate above a bound

`TenPositivePellOrdinateAbove.ordinate_dvd_above` proves that for every
IΣ₁ model, Pell parameter a, positive modulus N, and arbitrary **internal**
bound L, some internal index m>L has `N ∣ ycoord(m,a)`. It takes a positive
index supplied by `ordinate_dvd`, multiplies that index by L+1, and uses the
checked strong-divisibility theorem to carry the ordinate divisibility to the
larger index. No graph, halt, or iPRA endpoint is claimed.

Accepted guarded check `observations/above-attempt01/` produced
`/tmp/pell-ordinate-above-pfzhcfvr/PellOrdinateAbove.olean`, SHA-256
`23ae14ad8c173e11ee7cb4b6f10b10232ea7e627c12361e37fc29f8b29c62645`.
The selected pigeonhole and strong-divisibility direct objects are explicitly
resolved, hash-pinned, and rechecked before/after; Lean accepts them together.
Full transitive project/package, historical source-object and dynamic-library
coverage remains inherited.
