# Auxiliary sign and small-norm descent for the free-coefficient83 candidate

## Scope and source

The exact source is the packet in `complete83_free_coefficient_scout.json`, pinned by the author's note at commit `0d9d1e0174df30d82d80d758e9ba8e793203126e`. It has been read as data, not executed. All statements below refer to its exact paid definitions

- A = a+2 >= 3, Delta = A^2-1 > 0
- S = aux_coefficient_root > 0, f > 0, y = y_aux > 0
- V = c(T f-1)-R f^2, an integer of initially unrestricted sign
- d = norm_strong = Delta f^2-S^2
- N = norm_aux = S^2 V^2-(S^2-1)y^2
- the product of these and five other integer factors is Delta

No other factor is presumed to be a unit. Thus every factor is nonzero, divides Delta, and has absolute value at most Delta; in particular |d N| <= Delta.

## Elementary lemma, independent of all compiler assumptions

Let H >= 2 be an integer, v >= 0 and y > 0 integers, and N=H v^2-(H-1)y^2.

1. If N<0, then N <= -(H-1).
2. If 0<N<H, then N is a positive perfect square.
3. If N=-(H-1), every nonnegative-v solution is
   v=2(H-1) psi_(2H-1)(r), y=chi_(2H-1)(r), r>=0.

Here chi_B(r)+psi_B(r)sqrt(B^2-1)=(B+sqrt(B^2-1))^r.

Proof: For N<0, necessarily y>v. Set t=y-v>=1. Then

  -N=(H-1)t^2+v(2(H-1)t-v).

If v<=2(H-1)t, this is >=H-1. Otherwise, negativity says

  v < ((H-1)+sqrt(H(H-1)))t < (2H-1)t.

The integral transformation

  v'=(2H-1)v-2(H-1)y = v-2(H-1)t,
  y'=(2H-1)y-2H v = (2H-1)t-v

therefore has 0<v'<v and y'>0, and preserves N. Induction on v proves claim 1.

For 0<N<H, v>=y+1 would give N=H(v^2-y^2)+y^2>=H, so y>=v. If y=v then N=v^2. Otherwise t=y-v>=1, and N>0 gives v>2(H-1)t. Also v>=(2H-1)t would give N>=H t^2>=H: the quadratic in v is increasing beyond its positive root. Thus the same transformation has positive v',y' and smaller v. Induction proves claim 2.

For equality N=-(H-1), descend while v>2(H-1)t. At the terminal point the displayed expression for -N forces t=1 and v=0 or v=2(H-1). The latter maps to (0,1). Reversing the transformation yields the matrix [[2H-1,2(H-1)],[2H,2H-1]] iterates of (0,1), exactly the formula in claim 3. This proves classification, including v=0.

## Consequences from the full product equation

First S=1 is impossible: then d=Delta f^2-1>1 (Delta>=8), and d|Delta but gcd(d,Delta)=1, contradiction. Hence S>=2 and H=S^2>=4.

If N<0, the lemma gives |d|(H-1)<=Delta.

- If f>=2, the strong definition and |d|<=Delta give H>=3Delta, contradicting H-1<=Delta.
- Hence f=1 and d=Delta-H.
- If d<0, write b=-d>=1, so H=Delta+b. The inequality b(Delta+b-1)<=Delta forces b=1. Therefore S^2=Delta+1=A^2, S=A, d=-1, and necessarily N=-Delta.
- If d>0, Delta=H+d and d(H-1)<=H+d gives (d-1)(H-2)<=2. If d=1, then A^2-S^2=2, impossible for positive integers. If d>=2 and H is an integer square >=4, the only numerical possibility is H=4,d=2, giving A^2=7, again impossible.

Thus a negative auxiliary factor can occur only in the exact branch

  f=1, S=A, d=-1, N=-Delta.

The five untouched factors then have product 1 and are individually units. This conclusion is unconditional on parity of A and does not identify N<0 with V=0: the exceptional auxiliary solutions include every

  |V|=2Delta psi_(2A^2-1)(r), y=chi_(2A^2-1)(r), r>=0.

If N>0, it is always <S^2 and hence a perfect square. Indeed:

- for f>=2, S^2>=3Delta>Delta/|d|;
- for f=1,d<0, S^2>Delta>=Delta/|d|;
- for f=1,d>0, d cannot be 1 as above, and d>=2,S^2>=4 imply dS^2>Delta=S^2+d.

Together with |N|<=Delta/|d| this proves N<S^2 in every positive case.

## Pending review of the last exceptional branch

The source-specific five-unit bounds from the exact parent85 proof give R>0, R<Delta, c>A Delta^2, c>2R, and c=psi_A(p) with p>=25. The exceptional V formula and V=c(T-1)-R seem to contradict these bounds for both parities of p by reducing Pell sequences modulo c (odd p), or modulo c/(2A)=psi_(2A^2-1)(p/2) (even p). A separate detailed proof is being prepared. The unconditional results above do not depend on this final exclusion.
