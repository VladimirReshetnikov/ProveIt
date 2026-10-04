# Independent proof challenge: the determinant-negative U15 monoid obstruction

**PASS, no correction requested.** The new both-determinant-negative argument in Sections 3–4 of [u15_positive_monoid_parabolic_obstruction.md](u15_positive_monoid_parabolic_obstruction.md) is valid for arbitrary integer matrices A,B with determinant −1 whose positive words are injectively encoded. It does not assume free-group faithfulness. Together with the separately stated determinant-positive theorem dependency and the elementary mixed-determinant case, it supports the author's stated obstruction for W=(ab)^3b².

This is a focused independent proof audit of the delicate integral case, plus a complete read of the helper and the companion's scope. The published Jacques–Short classification used in Section 2 is an explicit inherited theorem; its full proof was not independently re-established in this review. No predecessor or archived program was executed.

## Authenticated final packet

| File | SHA-256 |
|---|---|
| u15_positive_monoid_parabolic_obstruction.py | `3822d6f8e4eaa23406e00c213635edacb73a6d6b5b045b09aa2e0ec060a5e1cd` |
| u15_positive_monoid_parabolic_obstruction.json | `5c01c892b863634b1d7b254c75b4ebaa64e9a9dd22fcd3a7bcb89ee262203518` |
| u15_positive_monoid_parabolic_obstruction.md | `d7dfe3134ccdbdb1632498f513e68b49e4a773eee52f74c2fea54d12a946fce9` |

Both pinned local proof dependencies were authenticated by fresh exact receipt replays from `/`, in normal and optimized Python. Both pass: ten complete coefficient identities and seven exact failed-faithfulness matrix fixtures. Those fixtures supplement, rather than establish, the unrestricted classification.

## Independent derivation and divisibility audit

A positive word cannot have finite-order image: two distinct positive powers would coincide, even without comparing to the empty word. Central sign changes preserve this obstruction, since squaring removes the sign. It is therefore legitimate to normalize the nonzero traces of the two determinant-negative letters to s,t>0. A zero trace would already make one letter an involution.

Set X=AB and x=tr X. Independently applying Cayley–Hamilton gives

```
B²=tB+I,
y0=t, y1=xt+s, y_(n+1)=x*y_n−y_(n−1),
y3=(x³−2x)t+(x²−1)s.
```

Thus `tr(X³B²)=t*y3+x³−3x`, exactly the author's cubic trace formula. Expanding `A^-1=A−sI`, `B^-1=B−tI` also gives the stated commutator trace `K=x²−stx−s²−t²−2`.

Integer |x|<2 makes X finite-order by its determinant-one characteristic polynomial, so it is forbidden. At x>=2 every term in the displayed positive expression makes tr W>2. At x=−2, trace +2 would require t²=2 modulo3; trace −2 forces 3s=4t and hence tr(X³B)=0. This last positive word has determinant −1 and squares to I. The boundary cases are therefore exhausted before any division.

For x=−z with z>=3, write `D=z²−1`, `N=z³−3z+2ε`, ε=±1. Solving the trace equation divides only by tD>0. Substitution yields

```
K=2−m², m=(t²+εN)/(tD).
```

Because K is integral and m rational, m is integral: writing m=r/s in lowest terms makes s² divide r², so s=1. Next `u=t/(z−ε)>0` is rational and satisfies the monic integer equation

```
u²−m(z+ε)u+ε(z+2ε)=0.
```

The rational-root theorem therefore makes u a positive integer. Neither conclusion silently assumes the desired divisibility or uses a finite search.

For ε=−1, `v=(z−2)/u=u−m(z−1)` is a positive integer and z−1=uv+1. Hence `m=(u−v)/(uv+1)`. Its absolute value is strictly less than one for all positive u,v, so m=0, u=v and K=2.

For ε=+1, m>0 and the second monic root `v=(z+2)/u=m(z+1)−u` is a positive integer. Thus uv>=5 and u+v=m(uv−1). Ordering u<=v loses no case. When u=1, integrality would require v−1 to divide2 despite v>=5. When u=2, the positive integer ratio (v+2)/(2v−1) is possible only at v=3. When u>=3, u+v<uv−1. The only surviving triples are consequently `(s,t,x)=(23,6,−4)` and `(34,9,−4)`.

## Why K=2 really forces a positive-word collision here

The statement is not being applied to arbitrary reducible real pairs. B has eigenvalues λ,μ in the real quadratic field Q(sqrt(t²+4)). This discriminant is not a square for t>0: a hypothetical square would give positive integer factors `(h−t)(h+t)=4`, whose only same-parity possibility makes t=0. The eigenvalues are distinct and irrational.

In a B-eigenbasis write A as `[[p,q],[r,s0]]`. Direct multiplication gives

```
tr(ABA^-1B^-1)=2−q*r*(λ−μ)²/(det A*det B)
             =2−q*r*(λ−μ)².
```

Thus K=2 forces q*r=0 and A preserves one eigenline. The matrices are rational, so the nontrivial quadratic Galois automorphism carries that invariant line to the other B-eigenline and also preserves A. Both eigenlines are therefore invariant. A and B commute, contradicting injectivity on the distinct positive words ab and ba. Moreover W is diagonal in that basis; determinant one and trace −2 then give W=−I, exactly as claimed. No hidden irreducibility or prior group-faithfulness assumption enters this step.

## Exceptional positive involutions and theorem boundary

For the two exceptional triples let U=XB and V=X²B. Their traces are (−1,−2) or (−2,−1), respectively, and `UV^-1=X^-1`. Since det V=−1, the two-matrix trace identity yields tr(UV)=tr U tr V+tr X=−2. Applying the determinant-negative characteristic equation gives trace zero for U²V in the first case and UV² in the second. Each is a positive word of determinant −1, hence an involution. Central sign normalization cannot remove the resulting positive-power collision. This closes both exceptional cases.

The mixed-determinant check `tr(W²)=tr(W)²+2` also has the required boundary: trace zero makes W²=I, while any other integer trace makes W² hyperbolic. In the determinant-positive portion, the companion explicitly handles proper interval containment rather than silently assuming interior containment. The word uses both letters, which is essential to that endpoint argument; no prohibition of a pure parabolic letter power is inferred.

The result concerns the fixed word W and faithful positive-word encodings into GL2(Z). Restricting a faithful twenty-letter encoding to its two tape letters is legitimate; conversely, faithfulness of only the tape pair would not validate the complete directed construction. No result is inferred about other repeated words, nonfaithful encodings, higher-dimensional matrices, or a completed ordinary-input Diophantine membership certificate. The packet introduces no universal arithmetic bound.
