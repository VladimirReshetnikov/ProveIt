# Small-coefficient growth majorant from constructor depth

This gives an independent check of the local label bound needed when the
derived-label range test is removed. Let t>=8, and suppose every local
parameter a,b,c,d is a natural number less than t. The square-shell
constructors are

```
I(x,y)=2((x+y)^2+x),       M(x,y)=I(x,y)+1,
A(x,y)=2((x+y)^2+3x+4y+3), E(x,y)=A(x,y)+1.
```

If 0<=x,y<s are integers and s>=1, monotonicity gives

```
I(x,y) <= 8s^2-14s+6 < 8s^2,
M(x,y) <= 8s^2-14s+7 < 8s^2,
A(x,y) <= 8s^2-2s < 8s^2,
E(x,y) <= 8s^2-2s+1 < 8s^2.
```

Thus any one constructor applied to arguments below t^e, e>=1, has output
below `8t^(2e)<=t^(2e+1)`. Set `e_0=1` and `e_(r+1)=2e_r+1`.
Then `e_r=2^(r+1)-1`; every constructor expression of depth r is less
than `t^e_r`. Constants zero and one satisfy the starting bound because
t>=8. M and E count as one constructor each, since their additive tag is
already included in the estimate. Write N(x)=I(x,1).

The nine original local axiom schemes have depths

```
4, 3, 3, 3, 3, 5, 4, 3, 19.
```

For the only large case, the recursive depth audit is

```
req(x,k,h):                       depth 7,
s=A(k,I(M(k,x),M(k,y))):          depth 3,
tail0=I(s,req(y,k,h)):            depth 8,
tail1=N(A(x,tail0)):              depth 10,
tail2=N(A(x,I(h,tail1))):         depth 13,
clos=A(y,I(M(y,k),tail2)):        depth 15,
nks=A(z,I(clos,N(req(y,z,z)))):   depth 17,
vrel=I(M(x,y),A(z,M(x,y))):       depth 3,
bundle=N(I(vrel,nks)):           depth 19.
```

The other labels occurring in the local modus-ponens/generalization rows
are parameters, I(a,b), and A(a,b), all of depth at most one. Therefore
EVERY local nonnegative formula label j satisfies

```
j < t^(2^20-1) <= t^ell,   ell=2^20.
```

For the balanced construction, let

```
t=128+4z^2,  K=t^4,  F=t^K.
```

Then t>=128 and `t^3>=2^21>ell+1`, so

```
(1+t^ell)^t <= t^((ell+1)t) < t^(t^4)=F.
```

This supplies the positive-coefficient budget in Section5 of
C_ANCHOR_THEOREM.md. It also implies `F+1>(t^ell)^t`, which is the
factor-count comparison needed before applying the coefficient budget.
No large fixed coefficient is inserted into the polynomial: K is computed
by two quadratic rows `T=t^2`, `K=T^2`; t has the quadratic cofinal form
above. The power F=t^K is interpreted by its finite Pell certificate.

The majorant is for the individual formula labels. It is not a claim that
the sum of all labels obeys the same strict bound; that unused derived sum
has been removed from the balanced construction.
