# Compact44 power-of-two q forces the rank divisible by 3

This is a small external arithmetic observation, submitted for independent
review. It authenticates the actual little-endian P72 compact44 ports used by
the free-J 88/30 graph and its proposed 86/26 fold. At these ports, **every
integer assignment with q a power of 2 has R divisible by 3**. It rules out
the specific noncanonical Pell seed with `R=3d−1` from
`../current14-free-gap-current-full-zero/` for this fixed port tuple, even if
J is allowed to vary. It does not rule out other Pell seeds, other q values,
positive 86 witnesses, or unrestricted zero-existence equivalence. No Lean,
iPRA or PDF/file-semantics theorem is claimed.

The free-J graph has

```
q = 1+J*beta,
G = J*beta*(q−F)+alpha,
R = G*(q²−1)+J*(MC+q*MF).
```

The authenticated payloads have `beta≡MC≡MF≡1 (mod 3)`. For q=2^t with
integer `t>=0`, q is 1 or 2 modulo 3, so `q²−1≡0`. If `q≡1`, then
`J≡q−1≡0` because beta≡1. If `q≡2`, then `MC+q*MF≡1+2≡0`. In either
case the second summand vanishes as well. Hence `R≡0 (mod 3)`.

This corrects two rejected overstatements in the accompanying alternate-port
attempt: the maintained carrier65 ports are not the compact44 ports, and the
proposed auxiliary completion is nonintegral. In the unrestricted domain q
may instead be 0 modulo 3; then the argument above does not apply. In fact,
the symbolic mod-3 graph permits R≡2 in that case, so the power-of-two
condition is essential to this observation.

The checker pins both P72 and P115 bindings and all four compressed and raw
payload hashes, checks the exact literal rank rows and 3-residue calculation,
and saves finite results. It does not rely on a historical Lean object.

Independent external review is recorded in
`../../reviews/ordinary13-compact44-power-rank-mod3-independent/`.
