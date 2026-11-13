# Positive parent zeros yield signed-fold zeros with negative Bt

This elementary argument is submitted for independent review. For any fixed
integer ports with **beta>0 and K0>=0**, every positive zero of the 88/30
parent yields a positive zero of the sign-reversed 86/26 candidate. The new
candidate can be chosen with **Bt<0**, and no positive parent first coordinate
is available while its other twelve coordinates are fixed. This proves one
existence direction without a halt premise or canonical-witness choice. It
does not settle the reverse existence implication: another parent zero with
different coordinates may exist. No Lean/iPRA, PDF or file-semantics theorem
is claimed.

## Extract the first root

Let a positive parent zero be given. Set

```
b=J*beta,  q=1+b,  M=q³*b,
C=q−F−alpha,  G=b*(q−F)+alpha,
Bt=C*(X+K0*q)−F*q,  m=X*Y²,  k=eta+zeta,  ell=m*k.
```

All b,q,M,X,Y,k are positive, q>=2 and k>=2; C, G and Bt are integers.
The 88 output is a sum of four squares, so its first residual gives

```
Z²=M²*(1+ell*(ell+k)).
```

Integer prime valuations imply M|Z. Set `tau=|Z|/M>0`. Since the literal
parent has

```
Z=M*(ell+k+r_old−k*Bt)+Y*b−q³*Bt,
```

reduction modulo q³ and b, with `gcd(q,b)=1`, gives `q³|Y` and `b|Bt`.
Write `Y=q³*s`, `Bt=b*t`. Furthermore

```
(ell+k)²−tau² = ell*k+k²−1 > 0,
```

so `tau<ell+k`. In fact Bt>0 on the starting parent zero: if Bt<=0,
then the literal Z expression gives `Z>M*(ell+k)>0`, contradicting
`|Z|=M*tau<M*(ell+k)`.

## Shift the scalar representation and choose sigma

Keep J and all inputs except F, alpha and the first-root coordinate fixed;
put

```
F' = F+b,               alpha' = alpha+b²,
C' = q−F'−alpha' = C−q*b,
G' = b*(q−F')+alpha' = G.
```

Thus F' and alpha' remain positive. The literal rank
`R=G*(q²−1)+J*(MC+q*MF)` is unchanged. Since F,alpha>=1 and b>=1,
`C<=q−2` and hence `C'<=−2`. Since X>0, K0>=0 and F'>0,

```
Bt' = C'*(X+K0*q)−F'*q < 0,
Bt'−Bt = −q*b*(X+K0*q+1).
```

In particular b|Bt'; write `t'=Bt'/b<0`. Define the new positive 86 input

```
sigma' = ell+k+s−t'−tau > 0.
```

The sign-reversed 86 graph has

```
Z' = M*(ell+k−sigma')+Y*b−q³*Bt' = M*tau.
```

Its first residual is therefore zero. All other residuals are unchanged:
the input changes affect them only through G and R, both of which are fixed;
all other inputs and ports are retained. Thus the new tuple is a strictly
positive signed-fold zero with Bt'<0.

## No fixed-other-coordinate positive parent repair

For these retained other coordinates, the first norm forces the signed
first expression to have root `+tau` or `−tau`, and the corresponding
candidate sigma values are

```
ell+k+s−t'−tau,      ell+k+s−t'+tau.
```

Both are positive. Since `k*Bt'<0`, either direct parent first coordinate
`r_old=k*Bt'−sigma` is negative. Hence no positive parent zero can share these
other twelve inputs. This conclusion is conditional on the starting parent
zero; it does not assert that either graph has a zero at compact44 ports.

The checker pins both graph sources, checks the scalar shift and the use sites,
and runs a small exact first-root/control tuple. It does not replace the
unbounded arithmetic proof or replay any Lean provider. The reverse existence
implication remains open.

Independent external review is recorded in
`../../reviews/ordinary13-folded-root86-negated-forward-independent/`.
