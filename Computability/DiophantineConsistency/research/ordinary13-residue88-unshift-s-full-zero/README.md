# A full zero when the 13/88 s shift is removed

The 87-row [probe](probe.json) is the [13/88 natural graph](../ordinary13-natural-residue-forced88-degree60/)
with the single operation `shift_s=n_s+1` deleted and its uses retargeted to
`n_s`. This packet gives a **full natural zero** of that probe with `n_s=0`,
including at the authenticated compact P72/P115 ports. It therefore disproves
any claim that the probe's equations force `s>0`. It is not a proof that the
probe and parent have different global zero-existence truth values, nor a new
consistency equivalence or iPRA theorem.

## Exact family

For any integers `beta>=3`, `K0,MC,MF>=0`, put

```
b = beta,  q=b+1,  h=ceil((K0+2)/b),
w = b*h-K0-1,  X=q*w,
R = (1+b²)*(q²-1)+MC+q*MF,
k = R+1,  t=(b-1)*(w+h)-1,  P=b*t,
r = k*(P-1)+t+1.
```

Here `w>=1`, `X>=1`, `R>0`, `t>=1` and `r>0`. In the probe use the following
natural inputs, written as the graph's semantic positive/shifted coordinates:

```
J=1, F=1, alpha=1, f=2, i=3, T=R,
w as above, s=0, r as above, eta=1, zeta=R, y=1, gamma=0.
```

For the literal JSON inputs, the shifted coordinates F, alpha, i, T, eta,
zeta use respectively `0,0,2,R-1,0,R-1`; the other coordinates take the
values displayed. With `s=0`, the actual graph has

```
Y=U=E=ell=0, c=1, a=0, H=Delta=3,
C=b-1, X=q*w, Bt=(b-1)*(X+K0)-1=b*t=P,
Q=9, I=3, V=-1, y²-Q*(y²-V²)=1.
```

The divisibility follows from `X+K0=b*(w+h)-1`. Also `k=R+1`, so the signed main expression `Dstar=3*(R+1-k)=0` and
its norm residual is zero. The first expression satisfies

```
Z=b*(k+r-k*P)-P=b,
Z²-b²*(1+ell*(ell+k))=0.
```

The strong residual is `I²-Q=0`, and the auxiliary residual is zero by the
identity above. Thus all four squared residuals, and the complete output,
are zero. No assumption about Con(ZFC) or a search heuristic is used.

## Evidence and scope

The checker reconstructs the probe from the pinned 88-row graph, evaluates
all 87 rows in an exact sparse integer polynomial ring under the parameterized
family, and verifies that each residual and output is identically zero. It
also authenticates the P72/P115 raw and compressed port hashes, constructs the
compact-port witness using exact integers, and checks its positivity and
family identities. To avoid writing giant decimal numerals, the receipt gives
only selected coordinate bit lengths. A small toy instance is additionally
evaluated through both complete graphs: the probe has zero while the parent
at the **same natural vector** does not. That toy comparison is not a claim
about all possible coordinate maps or the parent’s global zero existence.

From `Computability/DiophantineConsistency` run:

```
python3 -I -S -B research/ordinary13-residue88-unshift-s-full-zero/build.py
python3 -I -S -B research/ordinary13-residue88-unshift-s-full-zero/check.py
```

The deterministic checker output is [receipt.json](receipt.json). The family
is external exact arithmetic, not a Lean model theorem or an assertion about
the maintained current-2011 PDF.
