# An i-unshift full zero at positive natural ports

The 84-operation i-unshift probe derived from the [eta/zeta-natural 85-row graph](../ordinary13-eta85-zeta-zero-boundary-audit/probe.json) has a complete natural-input zero at the **positive natural** port tuple

```
(beta,K0,MC,MF)=(3,2,914,1).
```

It has `i=0`, while the shifted parent at the same inputs has positive output. This is stronger than the separately retained beta-negative example, but it is **not** the fixed compact tuple: in particular `MC=914` violates its required `MC<beta`. It does not disprove an existential witness map at compact ports or establish a consistency equivalence.

The exact finite witness is specified by the recurrence

```
Pell(A,0)=(1,0),
Pell(A,j+1)=(A*x+(A²-1)*y, x+A*y)  when Pell(A,j)=(x,y).
```

Use

```
q=4, X=2^35, w=X/4, Y=64, U=1024,
M=X*Y², a=Y*(X+1), H=3+4a,
(tau,yFirst)=Pell(2M+1,30),  k=2*yFirst,
(g,c)=Pell(a+2,35),           eta=c-Y*k,
R=1083, h=(X+1)/3,
r=tau-M*k-k+(3*k+1)*h,
gamma=(g-X-a*c)/H+(k-R-1)/U.
```

All displayed divisions are exact; the checker verifies `0<eta<k`, `r≥0` and `gamma≥0`. The resulting graph input tuple is

```
(1,0,1,1,0,0,w,0,r,eta,k-eta,1,gamma).
```

Its actual rank is `R=(2+(4-1)*3)*(4²-1)+914+4=1083`, the first root is `3*tau`, and the main root is `U*g`. Thus A0=A1=0. On the unshifted graph, i=0 and f=1 make Q=I=0, so the strong residual is zero; y=1 makes the auxiliary factor one. The output is zero. In the shifted parent, i=1 instead, so its strong residual is `c⁴` and its output is exactly `c⁴>0`.

The checker computes these ordinary integers directly—its witness coordinates are roughly 1,500 bits, rather than enormous fixed compact constants—and evaluates **all 84 child and 85 parent rows exactly**. It records a SHA-256 of the canonical decimal witness plus its bit lengths without printing the long numerals. From `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/ordinary13-eta-zeta84-unshift-i-positive-ports-zero/check.py | cmp - research/ordinary13-eta-zeta84-unshift-i-positive-ports-zero/receipt.json
```

This is an external finite-integer certificate, not a Lean proof or an iPRA endpoint.
