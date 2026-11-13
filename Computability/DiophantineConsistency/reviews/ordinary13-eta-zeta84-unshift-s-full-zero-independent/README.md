# Independent review: full-zero family after unshifting s

The author receipt reproduces, and a separate exact sparse-polynomial
interpreter evaluates **all 84 rows** of the pinned s-unshifted graph on the
proposed five-parameter family. The first and main residuals and strong
residual are identically zero, the auxiliary factor is identically one, and
the complete graph output is identically zero. This is an external exact
integer/ring check, not Lean elaboration or an iPRA result.

For each natural tuple with beta≥2 and K0, MC, MF≥0, let
`h=ceil((K0+2)/beta)` and `w=beta*h−K0−1`. The ceiling gives h≥1 and
1≤w≤beta. Therefore `t=(beta−1)*(w+h)−1≥1` and B=beta*t≥2. Also
`R=(1+beta²)*((beta+1)²−1)+MC+(beta+1)*MF` is at least 40, making
`n_T=R−1`, `n_zeta=R` and `r=(R+1)*(B−1)+t+1` nonnegative. All other
listed witness coordinates are 0, 1 or 2. The checker also tests 1,920
bounded natural tuples against every row; those controls supplement the
symbolic identity and inequalities.

With s=0, the exact graph has Y=U=ell=0, c=1, Delta=3, Q=9, I=3,
V=−1, Bt=B, Z=beta and Dstar=0. In particular the zero is the complete
product-factor output, not only a selected residual. The pinned compact tuple
source sets `beta=2^(67*8807)−1`, K0=K and the remaining ports to natural
values, so it satisfies the construction for every natural K without
expanding the giant numerals. This source-expression observation is not a
Lean-checked physical decimal/PDF binding.

The parent eta/zeta-natural 85 graph is nonzero at the reported toy family's
**same** tuple only. That observation does not exclude some other parent
witness, prove zero-existence inequivalence, or rule out a more involved
replacement-witness map. The full zero does show that positive s is not
forced in this changed graph at those compact ports. No compact endpoint,
model theorem, zero map, Lean build or provider validation is claimed.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-eta-zeta84-unshift-s-full-zero-independent/check.py | cmp - reviews/ordinary13-eta-zeta84-unshift-s-full-zero-independent/receipt.json
```
