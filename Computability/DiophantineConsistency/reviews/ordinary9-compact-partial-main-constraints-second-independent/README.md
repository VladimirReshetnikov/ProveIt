# Independent review: compact first-norm partial and main-index restrictions

The two reviewed packets give a valid standard-integer **partial construction** at the exact symbolic compact tuple and necessary conditions on any completion of its main norm. They do not establish that the main norm has a solution, a zero of the nine-variable equation, a reverse bridge to the original parent, or an iPRA theorem.

For `beta=q−1`, `q=2^(67*8807)`, write `K0=beta*rho^42+K′` and `t=(beta−1)/2`. The pinned kernel bound `0<K′<rho^5496` and exponent inequality make `w=t−K′` a positive natural. With J=F=s=1 and alpha=2, the actual carrier has C=beta−2 and

```text
X+K0 = beta*(w+rho^42)+t,
B=C*(X+K0)−1 = beta*(C*(w+rho^42)+t−1).
```

The displayed quotient h is positive. Independent sparse-polynomial expansion verifies this exact identity. The compact low digit makes the actual rank odd, so `n=(R+1)/2` is natural. The first Pell recurrence gives `k=2n+4M*sigma`; the specified natural r makes the literal first root `beta*tau`, not merely an abstract first-norm solution. Consequently A0=0. Since `M/U=q²w`, the literal main root is divisible by U for every natural gamma and its normalized value is exactly the expression in the reviewed packet. No main Pell norm is asserted.

If a main norm completion exists, standard Pell classification gives a unique nonnegative index m with the actual positive ordinate c. Its allowed interval is `Yk≤c<(Y+1)k`. For `Af=2XY²+1`, `A=Y(X+1)+2` and `B=2A−1`, the stated bounds `2A<Af`, `B>2(Y+1)`, and `B²>2Af`, together with the recurrence ordinate bounds, rule out m≤n and m≥2n. Thus `n<m<2n`. If an ordinate y_m has reached Yk, its next increment is `x_m+(A−1)y_m>k`; the eta interval has width k, so it contains at most one ordinate. This proves uniqueness conditional on a completion, not that the interval contains one.

For the actual signed graph root, the Pell recurrence gives `g−a*c≡2^m mod H`, and its conjugate is the modular inverse. The two root signs therefore require respectively `2^m≡X mod H` and `2^m*X≡−1 mod H`. The positive branch's congruence is sufficient for a natural gamma once c and the other partial data are fixed: `g−a*c>c>X`, so the quotient in the reviewed construction is positive. No corresponding gamma-positivity sufficiency is asserted for the negative sign.

The independent checker reconstructs K′ modulo each cited prime by coefficient accumulation and base-rho Horner evaluation, checks primality and multiplicative orders, obtains the four discrete logarithms using baby-step/giant-step, and independently combines them by generalized CRT. It confirms the positive class `m≡31198741 mod 46027358` and negative class `m≡37842296 mod 46027358`. These use two verified divisors of H only; compatibility of either class does not establish a main norm solution. Bounded recurrence controls supplement the uniform interval proof.

The checker also pins both source packets and reproduces their receipts. No huge compact Pell coordinate, Lean build, provider/axiom audit or fixed-parent equivalence was produced. From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary9-compact-partial-main-constraints-second-independent/check.py | cmp - reviews/ordinary9-compact-partial-main-constraints-second-independent/receipt.json
```
