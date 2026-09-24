# Replacing the cubic row radix by 8v gives a false 79-operation component

The 80-operation finite-history component in
[the two-auxiliary proof](EXPLORATION_TWO_AUXILIARY_HISTORY.md) uses
`W=v^3`, with `q=v*quot`, `q-1=H(W-1)` and `I+alphaI=v`. Its input
parameters `I,F` are arbitrary positive integers. Boolean endpoint
digits are a conclusion, not an input-domain restriction.

Replacing `W=v^3` by `W=8v` deletes one multiplication: omit `v2=v*v`
and replace `W=v2*v` by `W=8*v`. This gives a perfectly valid arithmetic
certificate of **79 operations, 45 multiplications and 34 additions or
subtractions**, with the same 29 positive unknowns and 19 equalities.
It does **not** preserve the endpoint relation.

## 1. An exact positive outer witness

Take

```
q = W = 16384 = 2^14,
v = 2048, quot = 8, H = 1,
C = I = 64, B = 512,
Y = F = 256,
U = 4104, V = 144,
alpha = 7680, alphaI = 1984.
```

Then `W=8v`, `q=v*quot`, `q-1=H(W-1)` and `B=8C`. Both local sides
are exactly

```
15B+4Y = C+2U+3V = 8704.
```

Their sum with `alpha` is `q`, and `I+alphaI=v`. The moving-time
equation is also exact:

```
I+WY=C+qF,
```

since `q=W`, `I=C` and `Y=F`. All twelve outer witnesses are positive.

The word `T=B+H=513` is Boolean in radix eight. Put

```
P=U+qV+q^2Y+q^3T,
L=q^6, lambda=(L-1)/7,
r=(L-P)(L-1)+6lambda,
D0=q^10, n0=q^5.
```

The binary support of `P` is exactly

```
{3,12,18,21,36,42,51}.
```

Every position is divisible by three, so `P` is Boolean in radix
eight. Every field is strictly below `q`, and `0<P<q^4<L`.
The unit bit of `U` vanishes, so `P` and `r` are even.

Nevertheless `F=256=4*8^2` has a forbidden radix-eight digit four.
It is not an encoded Boolean endpoint. Therefore no valid instance
of the 80-operation endpoint relation has these same input parameters.

## 2. The entire positive Pell tail can be supplied

This is not merely a local-rule alias. All hypotheses of the retained
43-operation positive Pell construction are satisfied:

```
n0=q^5>=64,
n0<r<q^12<n0^3,
r is even.
```

The mask has `L=8^28`. Since `P` is Boolean, the exact general-radix
mask theorem gives

```
popcount(r)=5*28=140,
v2(binom(2r,r))=140,
D0=q^10=2^140 divides binom(2r,r).
```

The finite checker evaluates the first identity and the displayed
inequalities directly. It does not attempt to materialize the enormous
central binomial coefficient or Pell witnesses.

The positive construction in
[the base-two Pell proof](BASE_TWO_PELL_90_PROOF.md) and
[the half-parameter proof](HALF_PARAMETER_PELL_92_PROOF.md) now supplies
all seventeen remaining positive unknowns. In particular, choose

```
J=2r+1,
U_pell=2^J,
Y_pell=floor((U_pell+1)^(2r)/U_pell^r),
w=U_pell/D0, s=Y_pell/D0,
a=Y_pell(U_pell+1), A_pell=a+2,
c=psi_(A_pell)(J), d=chi_(A_pell)(J),
k=psi_(2U_pell*Y_pell^2+1)(r+1).
```

Power-of-two divisibility and the mask theorem make `w,s` positive
integers. The proved strict ratio bounds and congruences supply
positive `eta,zeta,tau,h,gamma`; even `r` supplies the positive
relaxed and half-parameter witnesses `i,f,j,o,y_aux`. None of these
ten source equations contains `v`, `W`, or an endpoint digit test.
Their unchanged preconditions depend only on the bounds, divisibility
and parity just established.

Consequently this outer tuple extends to a positive solution of all
19 equations of the 79-operation variant. Its invalid output `F`
refutes that variant's claimed finite-history semantics.

## 3. The alignment mistake

After the Pell argument, the modified geometry still proves that
`q` and `W` are powers of two and `q=W^t`. It no longer immediately
proves they are powers of eight. Here `t=1` and their exponent is 14.

Although `P` is Boolean in radix eight, its base-q fields begin at
binary positions `0,14,28,42`. Only the first and fourth boundaries
are aligned to radix-eight digits. The second field can have its
bits at positions congruent to one modulo three, and the third at
positions congruent to two modulo three. These are exactly the
phases of `V=144` and `Y=256` in the example.

In the one-row case, the temporal equation and bounds force
`C=I,Y=F`. It would be circular to use `F`'s Booleanity to repair
the alignment: establishing that Booleanity was one of the required
conclusions. The example has valid initial digits and invalid final
digits, so even restricting only the initial word to Boolean digits
does not repair the proposal.

The published 80-operation construction retains `W=v^3`. No frozen
certificate or proof was changed by this exploration.

## 4. Reproducible checks

[The exact checker](../verification/explore_affine_row_radix_counterexample.py)
expands every primitive of the modified 79-operation schedule and
matches all 19 source residuals, including the single triangular
auxiliary correction. It separately checks the nine positive outer
equations of the counterexample, all four field bounds, exact packed
support, parity, popcount and every retained Pell size hypothesis.
Its [JSON receipt](../verification/explore_affine_row_radix_counterexample.json)
marks the arithmetic as passing and the endpoint relation as refuted.

The full-system existential extension uses the cited general positive
Pell theorem. It is not described as a finite numerical instantiation
of its huge witnesses.
