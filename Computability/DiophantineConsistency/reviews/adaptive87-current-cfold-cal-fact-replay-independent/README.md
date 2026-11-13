# Independent review: C-fold Cal fact replay

No concrete gap was found in the stated **standard-integer** derivation of
`X>=q²`, assuming the cited Pell and rank-window theorem statements in the
standard naturals. This is a mathematical/source-interface review, not a Lean
replay, current-provider authentication, all-IΣ₁-model proof, internal iPRA
proof or physical-document binding. The current port inequalities and byte
bindings remain inherited from the separately pinned checks.

The author has strengthened the candidate checker to bind all 88 graph rows;
that receipt reproduces. This review independently checks 59 relevant rows,
including the first/main parameters, rank, strong equation and signed
auxiliary root; it checks source interfaces, 1,536 signed-absdiff controls,
and exact free-ring scale and final projection identities. Its checker does
not mechanically verify the universal Pell theorem applications.

## Index and auxiliary hypotheses

The first norm and positive `m=X*Y²` give one first Pell index n with both
`tau=xcoord n B` and `k=2*ycoord n B`, where `B=2(m-1)+1`. Applying the
residue-quotient theorem to **that same n**, with divisor `2m=B+1`, gives a
natural w satisfying `k=2n+4mw`. The positive main root d obtained by the
previously reviewed orientation argument gives one main index p with both
`d=xcoord p a` and `c=ycoord p a`.

The rank-window hypotheses match positive beta, J, F, alpha, the two mask
inequalities, `q=beta*J+1` and `F+alpha<q`. The resulting upper window and
`q⁴ | R+1-k`, together with `q⁴ | 4m`, give `R+1<q⁴` and
`2n mod q⁴=R+1`. The lower estimate gives `R>=26`.

The `P72Exact.indices_ordinary` instantiation uses quotient `Y/q³` for its
first `y0` argument and the distinct w for its later quotient argument. Its
first-index parameter is n and main-index parameter is p. Its strong norm
is `I²+Delta=Delta*f²`, with `I=i*c²`. For the auxiliary equation, setting
`A=f²*(T*c)` and `B=f²*R+c` makes the two required natural absolute
differences `|V|=|A-B|` and `|V+u|=|A+u-B|`; rearranging Cal's signed
auxiliary equality gives the theorem's exact equality. No sign of V or V+u is
needed. These checks supply all displayed hypotheses and give the same-index
conclusions `13<=n`, `p=R`, and `2n=R+1`.

## Divisibility and power recovery

With `W=4*X*q*s*w`, the exact identity `4*m*w=U*W` converts the oriented
main balance into `q*(d+H*W)=q*(X+a*c+H*gamma)+H*X`. Since `H≡3 (mod q)`,
this implies `q|3X`; positive X and `q>=47` imply `X>=16`. Set `r=n-1`.
The same first and main indices now meet the `power_bound` interface, yielding
`2^R<Y`; its conditions `zeta>0`, `c=Y*k+eta`, and the two exact coordinate
identities have been tracked explicitly.

For `L=(H-3)/q`, multiplying the balance by L yields
`H | 3*(d-X-a*c)`. The independent checker verifies this implication's
underlying polynomial identity with L independent of the other variables.
The projection theorem, at the **same p=R**, gives
`d=2^R+a*c+H*z`; hence `H|3*(2^R-X)`. No division by 3 is used. Since
`X<a`, `2^R<Y<=a`, and `H=4a+3`, both `3X` and `3*2^R` lie in `[0,H)`;
the congruence forces `X=2^R`. Finally `R>=q³>=q` and `q>=47` give
`X=2^R>=2^q>=q²`.

This review accepts the referenced theorem statements and their standard
natural interpretation as premises; it does not establish that the retained
source/object/provider chain is coherent for a new build. Transporting the
argument to arbitrary IΣ₁ models and assembling syntactic iPRA derivability
remain separate work.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/adaptive87-current-cfold-cal-fact-replay-independent/check.py | cmp - reviews/adaptive87-current-cfold-cal-fact-replay-independent/receipt.json
```

No Lean, build, staging or modification of author evidence was performed.
