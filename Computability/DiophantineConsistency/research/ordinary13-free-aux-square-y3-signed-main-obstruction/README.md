# Signed main-root obstruction for the compact y₃ slice

The [stronger partial construction](../ordinary13-free-aux-square-main-norm-nonsquare-partial/README.md) has a natural main Pell root at `c=y₃`, together with nonsquare auxiliary input and correct strong/auxiliary factors. Its **actual signed main graph root cannot satisfy the main norm** at the selected fixed compact tuple. This rules out completing that particular `X=q, s=1, c=y₃` slice; it does not exclude other main ordinates or all zeros of the free auxiliary-square candidate.

Let q be the fixed compact power of two, q>8; X=q, Y=q³, U=q⁵, a=Y(q+1), A=a+2 and H=4a+3. For

```
c=y₃(A)=4A²−1,    g=x₃(A)=4A³−3A,
```

we have `g²−(A²−1)c²=1` and the exact identity

```
g−a*c = H*(2A+2)+8.                    (1)
```

If the actual graph main residual were zero, U²|Dstar² would imply U|Dstar. Its literal zero-shift formula is

```
Dstar=U*(q+a*c)+H*(U*gamma+R+1−k).
```

Since q is a power of two and H is odd, gcd(U,H)=1; the previous divisibility forces `U | R+1−k`. Thus the signed integer `d=Dstar/U` satisfies `d−a*c≡q (mod H)`. The norm says d²=g², hence d=g or d=−g.

If d=g, (1) gives `H | q−8`, impossible because `0<q−8<H`. If d=−g, the norm also gives `(g−a*c)(g+a*c)=1+H*c²`; together with (1) this implies `8(g+a*c)≡1 (mod H)`. The signed-root congruence then implies `H | 8q+1`, again impossible because `0<8q+1<H=4q³(q+1)+3`. Both signs are covered, and R, k, gamma and the auxiliary construction need no additional bounds for this contradiction.

As in the separately checked [main-factor unit argument](../ordinary13-free-aux-square-partial-main-obstruction/README.md), any ordinary-integer product-output zero forces A1=0: all factors are ±1 and `1+A1` cannot be −1 modulo four. Therefore no complete zero can occur in this selected y₃ slice. The natural norm `g²=1+Delta*c²` remains true; it is the **actual signed graph root** that is incompatible.

The checker reproduces the two predecessor receipts, verifies the actual child main-root rows and the x₃/y₃, norm and signed-congruence identities as exact integer polynomials, and checks bounded signed-root controls. These finite checks supplement the general divisibility proof above. No large fixed number, Lean process, build, provider/axiom replay, global zero-existence result or PDF binding is involved. From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-free-aux-square-y3-signed-main-obstruction/check.py | cmp - research/ordinary13-free-aux-square-y3-signed-main-obstruction/receipt.json
```
