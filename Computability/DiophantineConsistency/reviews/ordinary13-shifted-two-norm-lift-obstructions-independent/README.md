# Independent review of two-norm lift obstructions

The reviewed standard-integer implications are sound for the actual shifted two-norm graph at the pinned compact beta with J=1. The main norm alone gives `gcd(w,H/gcd(s,3))=1`, excluding the stated `w≡0, s≡1 (mod 5)` slice. If a two-norm zero has `w=1, s≡2 (mod 5)`, both signs of its actual main root give `m≡1 (mod 4)`, so the separately proposed `m≡3` sufficient lift cannot be used unchanged there. Neither observation proves that a zero exists in the latter slice, that no other lift exists, or that all graph zeros are excluded.

## Root divisibility and graph wiring

The independent checker follows the literal rows for the two norms and the root. They give `q=1+beta*J`, `X=q*w`, `Y=q³*s`, `U=Y*q²`, `a=Y*(X+1)`, `H=4a+3`, `Delta=a²+H`, and

```text
Dstar = U*(X+a*c) + H*(U*gamma+R+1−k).
```

All differences are integer-polynomial subtraction. Since U>0, `A1=0` and integer square divisibility give `Dstar=U*d` and `d²−Delta*c²=1`. H is odd and coprime to the power-of-two q, while `H≡3 (mod s)`. Therefore `gcd(H,U)=gcd(s,3)=g`. Cancellation after dividing by g is valid and gives `d−a*c≡X (mod H/g)`. The norm yields `(d−a*c)*(d+a*c)=1+H*c²`; hence the first factor, and therefore X, is a unit modulo H/g. Since q is a unit there, w is a unit too. The modulus is greater than one, so this also forces w>0.

The pinned exponent satisfies `67*8807≡1 (mod 4)`, hence `q≡2 (mod 5)`. If `w≡0, s≡1`, then `H≡0 (mod 5)` and 5 still divides H/g because g is 1 or 3, contradicting coprimality. This argument does not use the first norm, a Pell-index identification, or a constructed zero.

## First-norm and signed-root indices

After w>0, set `M=XY²>0`. At `A0=0`, the literal first norm has the standard positive Pell representation with ordinate k for multiplier `2M+1` and nonsquare `M(M+1)`; all such ordinates are even. This use of standard Pell classification is a mathematical input, not a new Lean result. From the displayed root identity and `Dstar=U*d`, `q⁵` divides `H*(R+1−k)`; q is coprime to H and `q⁵ | U`, so `q⁵ | R+1−k`. Thus R is odd. For the even main multiplier `A=a+2`, its Pell recurrence modulo two gives `c≡m (mod 2)`. Consequently the **stronger** condition `c | (R−m)` implies m odd. It does not follow that this divisibility holds, and this observation alone does not prove the more general gcd lift condition.

When w=1 and s≡2, `X≡2`, `a≡3`, `H≡0`, and `A≡0` modulo 5. The main Pell norm implies

```text
x_m−a*c ≡ 2^m,    x_m+a*c ≡ 2^(−m)  (mod 5).
```

For the positive root, the actual congruence is `2^m≡2`; for the negative root it is `−2^(−m)≡2`. The pairs of residues for m modulo 4 are `(1,4), (2,2), (4,1), (3,3)` respectively, so **both** equations hold only at m≡1. The inverse exists because 2 is a unit modulo 5. No assumption m=R or choice of positive signed root is used.

The checker pins the relevant sources, reproduces the reviewed receipt, checks the complete literal operand chain behind both norm identities and the signed root, and independently tests the two signs with modular Pell recurrence. Its finite gcd and parity grids are controls for the general arguments above, not their proof. Reproduce from `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-shifted-two-norm-lift-obstructions-independent/check.py | cmp - reviews/ordinary13-shifted-two-norm-lift-obstructions-independent/receipt.json
```

No Lean, build, staging, provider validation, arbitrary-model theorem or iPRA result was produced.
