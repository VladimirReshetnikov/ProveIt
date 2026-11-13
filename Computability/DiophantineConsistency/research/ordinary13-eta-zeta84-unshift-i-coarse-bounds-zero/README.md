# A symbolic i-unshift zero satisfying the coarse compact port bounds

The 84-row graph obtained by deleting `i=n_i+1` from the [eta/zeta-natural 85-row parent](../ordinary13-eta85-zeta-zero-boundary-audit/probe.json) has a standard natural-number zero at

```
(beta,K0,MC,MF)=(127,87,54,139).
```

These are **not the fixed compact constants**, but they satisfy the commonly used coarse constraints: beta≥46, K0>0, MC<beta, beta≤MF<2beta, beta≡7 (mod 8), beta≡1 (mod 3), MC≡6 (mod 8), and `MF-beta≡4 (mod 8)`. The witness has i=0 and the shifted parent at the same tuple has output `c⁴>0`. Thus none of those coarse port facts alone can prove pointwise i positivity for this deletion. It does not disprove an existential witness replacement or settle the actual fixed compact tuple.

All huge values below remain symbolic. Use the Pell recurrence

```
Pell(A,0)=(1,0),
Pell(A,j+1)=(A*x+(A²-1)*y, x+A*y)  when Pell(A,j)=(x,y).
```

Choose

```
L=2172, n=L*(2L+1)=9437340, m=n+L=9439512,
q=128, X=2^m, w=X/q, Y=2^L, s=Y/q³,
F=119, alpha=8, C=q-F-alpha=1,
M=X*Y², U=Y*q², a=Y*(X+1), H=3+4a,
(tau,yFirst)=Pell(2M+1,n), k=2*yFirst,
(g,c)=Pell(a+2,m), eta=c-Y*k.
```

The graph's actual signed rank is the natural number

```
R=(alpha+(q-F)*beta)*(q²-1)+MC+q*MF
 =1151*16383+54+128*139=18874679=2n-1.
```

The first Pell recurrence gives a natural `sFirst` with `k=2n+4M*sFirst`. Since `m≡5 (mod 7)` and `beta=2^7-1`, `X≡32 (mod beta)`. The actual first carrier is `B=C*(X+K0)-F=X-32=beta*h` for natural `h=(X-32)/beta>0`. Set

```
r=tau-M*k-k+(k*beta+1)*h,
gamma=4*(M/U)*sFirst+(g-X-a*c)/H.
```

Both are natural. Indeed `tau>M*k`, `M/U=2^(m+L-14)` is an integer, and the main Pell recurrence gives `g-a*c≡2^m=X (mod H)` with `g-a*c≥c>X`. The literal roots are then `Z=beta*tau` and `Dstar=U*g`, so the first and main residuals vanish.

To verify the required parent-coordinate bounds, put `P=2XY` and `Q=4XY²`. The chosen exponents satisfy the exact identity

```
P^(m-1)=2Y*Q^(n-1).
```

For every multiplier A≥2, the Pell ordinate satisfies `(2A-1)^(j-1)≤y_j≤(2A)^(j-1)`: the recurrence gives `A*y_j-x_j=y_(j-1)` and the ordinates increase. Applying this to the two multipliers gives `c>Y*k`: the main lower-base relative increment over P is `(2Y+3)/(2XY)>1/X`, while the first upper-base relative increment over Q is `1/(2XY²)<1/X`, and m>n.

For the upper bound, `c/(Y*k)≤(1+2/X)^(m-1)`. As `m<2^24` and `L+26<m`, we have `4(m-1)Y<X`; the geometric-series bound `(1+u)^j≤1/(1-j*u)≤1+2j*u` for `0≤j*u≤1/2` yields `c<(Y+1)k`. Hence `0<eta=c-Y*k<k`, and `zeta=k-eta` is a natural input.

Set `f=1`, unshifted `i=0`, `T=1` and auxiliary `y=1`. Then `Q=I=0`, the strong residual is zero and the auxiliary factor is +1. The complete natural input tuple is

```
(1, F-1, alpha-1, 1, 0, 0, w, s-1, r, eta, k-eta, 1, gamma).
```

All four factors are +1, hence the child output is zero. The parent substitutes i=1 at the same tuple, giving strong residual `c⁴` and output `c⁴>0`. This is a pointwise counterexample, not a statement that the parent has no other zero.

The checker pins the exact graphs, verifies the finite port/rank/exponent arithmetic and free-ring root identities, and directly evaluates a much smaller q=4 instance of the same power-matching construction through **every** parent and child row. It does not iterate the 9-million-step Pell recurrences or expand X, c or the fixed symbolic witness. The uniform interval and Pell arguments above are the proof of the large example; finite controls do not prove them. No Lean, provider, iPRA or PDF result is claimed.

From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-eta-zeta84-unshift-i-coarse-bounds-zero/check.py | cmp - research/ordinary13-eta-zeta84-unshift-i-coarse-bounds-zero/receipt.json
```
