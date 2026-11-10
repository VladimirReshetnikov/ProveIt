# Restricted reverse map for the 64-gate candidate

This gives a necessary-and-sufficient test for a **particular** reverse map:
preserve `q`, rank `R`, `w`, all four ports, and every other coordinate
except `F,C,z` (replacing the candidate's `C` with the old positive `alpha`).
It does not establish general reverse zero-existence equivalence. A different
map could change the coordinates held fixed here.

Suppose `q>=2`, `M=K+w>0`, and a positive candidate assignment has `Nt=1`.
Put

```
b = q-1,       G = q*(q-F)-C,
G = b*u+r,     0 <= r < b       (Euclidean division).
```

There is an old positive scalar tuple with the same `q`, `R`, `w`, ports,
and `Nt=1` **if and only if**

```
2 <= u <= b,       1 <= r < u,
t = M*(u-r) - (q-u) is a nonnegative multiple of b.
```

If it exists, that tuple is unique:

```
F_old=q-u,   alpha_old=r,   C_old=u-r,   z_old=1+t/b.
```

Indeed, the old positive inequalities `F_old,alpha_old,C_old>0` imply
`2<=q-F_old<=b` and `1<=alpha_old<q-F_old<=b`. Its gap
`G=b*(q-F_old)+alpha_old` is therefore exactly the Euclidean decomposition
above. Rank is injective in the gap when `q` and the ports are fixed. The
old transport equation `Nt=1` is exactly
`b*(z_old-1)=M*C_old-F_old`, giving the final two requirements and the
unique `z_old`. Conversely these formulas yield positive old inputs with
the same gap, rank and transport value. Every other gate then has the same
value, so a full candidate zero satisfying the criterion maps to a full old
zero. This proof uses ordinary integer arithmetic, not a Lean theorem.

The transport congruence has another useful form. If `u0=q-F` and
`d=u0-u`, then equality of the gaps gives `F_old=F+d` and
`C_old=C-q*d`. Candidate transport gives
`M*C-F` divisible by `b`; the old transport condition is equivalent to

```
b divides d*(M+1),
```

plus positivity of the resulting `z_old`. This is the same arithmetic shear
as in the proposal packet, now with the only possible `d` determined by
Euclidean division.

The guard `q-F-C>0` from the direct coordinate map is sufficient but not
necessary for this restricted repair. For example, at the *illustrative*
scalar values `q=4, M=2, F=1, C=5, z=4`, candidate transport is 1 and
`q-F-C=-2`; the unique old scalar repair is
`F_old=2, alpha_old=1, C_old=1, z_old=1`. This example does not assert
the other norm factors or any fixed-port full zero.

Conversely, the actual-port first-Pell partial construction in
`../current14-carrier64-transport-proposal/` has `G=(q-1)²-2`, so the gap
conditions give `u=q-2`, `r=q-3`, but its `M` fails the required transport
congruence. Thus this exact restricted repair cannot map that partial
assignment back even though the transport and first Pell norm can both hold.
The other norms are unresolved; no full candidate zero is claimed.

There is an even stronger fixed-port partial construction: the gap condition
itself can fail while both transport and the first Pell norm hold. Set

```
J=F=s=1, q=beta+1, C=2q-1,
w=1+(q-2)*K, z=3+K*(2q-1).
```

All these inputs are positive, `Nt=1`, and `q-F-C=-q`. Now
`G=b²-b-1=(b-2)b+(b-1)`, so `u=b-2`, `r=b-1`, and the required inequality
`r<u` fails. The checker verifies on the actual fixed ports that `R` is odd
and `1<R<q⁴-q³<E`. Consequently the same Pell construction from the
proposal packet applies: set `m=E*q³`, `j=(R+1)/2`, and take the coefficients
`(x,k)` of `(2m+1+2√(m(m+1)))^j`. The proven congruences yield positive
`n=(x-k+R)/E`, and `eta=1, zeta=k-1` makes the first norm 1. The Pell power
is specified symbolically, not expanded. No choice of old positive `F,alpha`
at the same `q` can have that rank, regardless of `w` or transport repair.
The other norms are still unsolved, so this does not produce a full candidate
zero or disprove a reverse map that changes `q` or `R`.

## Remaining main norm as two Pell indices

For the latter fixed-port scalar family, write `Y=q³`, `E=w*q⁴`,
`X=w*q`, `a=E+Y`, `H=4a+3`, and `m=E*Y`. For an integer `p>=2`, define
`chi_p(t), psi_p(t)` by

```
chi_p(t) + psi_p(t)*sqrt(p²-1) = (p+sqrt(p²-1))^t.
```

All first-norm solutions have `k=2 psi_(2m+1)(j)` and
`|tau|=chi_(2m+1)(j)` for some `j>=1`. In this family `R<E` and `n>=1`,
so `tau=E*n+k-R>0`. Since `E` is even, the carrier has a positive integer
`n` exactly when `2j=R+1 (mod E)`; the resulting
`n=(chi_(2m+1)(j)-k+R)/E` is positive. The original symbolic example chooses
`j=(R+1)/2`, but infinitely many positive indices satisfy the congruence.

The main norm has `Delta=(a+2)²-1`. Every positive solution has
`D=chi_(a+2)(r)` and `c=psi_(a+2)(r)` for some `r>=1`. This follows by
descending with the inverse unit: for a solution `D,c>0`,
`(p-1)c<D<=p*c` with `p=a+2`, so the new ordinate `p*c-D` is nonnegative
and strictly smaller than `c`; the descent ends at `(1,0)`.

For any such pair `j,r`, the positive `eta,zeta,gamma` satisfying the main
factor and its actual carrier exist exactly when

```
Y*k < c < (Y+1)*k,
D > X+a*c,                 D = X+a*c (mod H).
```

Then `eta=c-Y*k`, `zeta=k-eta`, and `gamma=(D-X-a*c)/H`. This is an exact
arithmetic reformulation of the next unresolved main-norm step, not a claim
that suitable indices exist. Even a pair satisfying these conditions would
leave the strong and auxiliary norm factors to solve. The checker verifies
the main Pell unit-step norm identity symbolically; the prior proposal checker
verifies the first-Pell congruence induction. Neither is a Lean proof.

The independent finite test enumerates `2<=q<=12`, `1<=M<=20`, and
`1<=F,C<=15`. Among 12,695 positive candidate scalar assignments satisfying
`Nt=1`, it compares the criterion with brute enumeration of every positive
old scalar choice: 661 have a restricted repair and 12,034 do not. These are
checks of the elementary criterion, not a search over complete norm solutions
or evidence about the fixed-port existence question. The script also verifies
the current compressed and raw port hashes and checks the cited fixed-port
congruence obstruction.

From the DiophantineConsistency directory:

```sh
python3 -I -S -B research/current14-carrier64-scalar-repair/check.py > /tmp/carrier64-repair.json
cmp /tmp/carrier64-repair.json research/current14-carrier64-scalar-repair/result.json
```

No Lean process, native proof replay, or PDF interpretation is performed.
The independent external review is in
`../../reviews/current14-carrier64-scalar-repair-independent/`.
