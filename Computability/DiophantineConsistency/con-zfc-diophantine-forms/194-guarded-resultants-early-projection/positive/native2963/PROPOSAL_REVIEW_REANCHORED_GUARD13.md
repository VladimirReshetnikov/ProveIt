# Reanchored joint guard: thirteen integers, degree1072

The guard supplement in `con_zfc_batched_certificates_2026-10-23.zip`
lowers the root-fusion CRT equation's degree from1088 to1072, retaining
all13 unrestricted integer variables,195 live operations and the entire
six-leaf source34 tuple. Its new ordinary argument is sound. This review
excludes the separate direct667/1690 components of the same archive.

For integer x,y,t put `Pair(x,y,t)=xy-(t²-x-y+1)²`. The assertion
`exists t, Pair(x,y,t)>0` is equivalent to `x>0 and y>0`: a positive
value forces xy positive; if both inputs were negative, the subtracted
square would exceed xy. Conversely, for `N=x+y-1>=1`, a nearest integer
square has squared error strictly below N, while `N<=xy`.

The form `Pos=1+p1²+p2²+p3(p3+1)` represents exactly the positive
integers, by Legendre's theorem applied to4n-3. Hence both existential
guards

```
v² Pair(G,T,t)=Pos,       Pair(v²G,T,t)=Pos
```

express precisely `v!=0,G>0,T>0`. This is an existence equivalence;
the guards are different polynomials with different private witnesses.

The new norm uses the second guard with T=eta*zeta. Its other four
radicands retain their unconditional strict positivity, so at a norm
zero the new guard radicand must first be nonnegative. The guard lemma
then restores the same signs and nonzero v before any root extraction.
Its radicand still satisfies `Ag<v²G eta*zeta`, exactly the upper bound
used by the parent's superincreasing-root proof. Thus the parent's
rational-root descent, CRT recovery and native kernel reconstruction
apply in their original order, including the v=0 and c=0 exclusions.
Completeness chooses new private guard witnesses and then a new free
norm center; it does not reuse an arbitrary old guard carrier.

Putting v² inside the lower-degree argument removes two degrees from
the dominant guard radicand. The complete biquadratic cut has unique
highest scalar component of weighted degree268, giving final degree
1072. The attained coefficient is `2^976 3^640 beta^480` at
`j^480 w^160 v^192 h^32 r^64 c^128 z^16`. The exponent sum is1072,
and the coefficient is positive at the authentic fixed beta. The
195-operation total is unchanged; this improves degree alone.

The [read-only review tool](tools/review_reanchored_guard13.py) pins the
whole new ZIP and the already reviewed root-fusion ZIP. Every93 inherited
file is byte-identical. Exact term interning checks that the **complete
norm** is unchanged over the single free guard-radicand cut; a mutated
norm is rejected. In isolated scratch, both normal and optimized builders
reproduce the supplied equation byte-for-byte and both complete auditors
pass the exact cut/leading-form calculation, all actual fixed coefficients
and independent formal-conjugate diagnostics. The
[receipt](data/reanchored-guard13-review.json) preserves both scopes.
Ten thousand positive-pair controls supplement the universal guard proof.

The inherited ordinary native/Pell/refutation theorem remains explicit.
Neither these finite checks nor the new guard lemma assert consistency
or constitute a new Lean/internal object-ZFC derivation. Lean is paused.
