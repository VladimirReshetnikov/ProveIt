# The period-divisor equation cannot be deleted from the window-copy certificate

Deleting `P*v=q` from the [80-operation system](FIXED_RAW_UNIVERSAL_80_PROOF.md)
produces a **false 79-operation candidate**, even when its remaining temporal
alignment equation is retained. The failure occurs for the actual compiler of
a fixed machine that accepts no inputs: the weakened system has strictly
positive witnesses at raw input **x=1**.

The weakened source has **79=42M+37A**, **32 positive existential coordinates**
and **20 equations**. It removes only the instruction `Pv=P*v`, its comparison
with q, and the unused coordinate v. All other geometry, native masks,
transport, kernel and raw-input equations remain. The
[checker](../verification/explore_window_copy_period_divisor.py) and
[receipt](../verification/explore_window_copy_period_divisor.json) audit this
full source. This is a rejection of a particular deletion, not a lower bound
on all possible certificates.

| Retained part | M | A | Total |
|---|---:|---:|---:|
| Outer source after deleting the divisor equation |10|12|22|
| Fixed-minus kernel |25|18|43|
| Raw-input bridge |7|7|14|
| **Weakened, false system** |**42**|**37**|**79**|

## 1. Actual fixed constants for an empty machine

Take the stay-step machine of the 80 proof, with initial transition
`(q0,1) -> (q1,2,stay)`, followed by entry into an absorbing nonhalting loop.
The distinguished halt state is unreachable. It accepts no unary input and
therefore no raw positive x. Its two fixed allowed windows Start and End are
exactly those of the 81 proof. A third distinct allowed window consists
entirely of unphased, headless blank interior tiles. Thus its full finite
allowed-window alphabet has at least three members.

Apply the effective compiler of the 80 proof to that entire alphabet,
enumerating End as selector0, Start as selector1, and any other allowed
window as selector2. All the constants in the construction below are the
resulting actual fixed compiler constants. They are not chosen to match a
particular numerical toy instance.

Write R for its inner radix, B=2^d for the cell radix, and

    K=DC+B*DR, CS=R, c0=1+R+R^2.

The compiler supplies the following properties:

* B and R are powers of two, B>R^3, and d>=4.
* K is even. Indeed every exponent in DC is positive, and DR and B are
  even; hence DC+B*DR is even.
* Selector2 is permitted in the native remainder Z, so `R^2 AND MC=0`.
* MF has no bits in inner-radix degrees0,1,2, so `c0 AND MF=0`.
* MC is odd, MF is even, both are positive and at most B-2, and their
  binary populations sum to d.

These claims follow directly from the compiler layout: its copy positions
begin at k+3a, its clause band lies higher still, and all tested positions
are strictly above the three low selector positions. This use of selector2
does not assume anything about the selected window's copies.

## 2. A complete positive outer tuple

Choose the following finite, though astronomically large, integers:

    N=K+B,                  q=B^N,
    J=(q-1)/(B-1),          P=J-K,
    align=(P-1)/(B-1),      x=1,
    W=B,                    Z=R^2,
    C=B+R+R^2=(B-1)+c0,     F=c0*J,
    z=1,                    alpha=q-C-d.                 (1)

Since B is1 modulo B-1, the repunit J is N modulo B-1. Also

    N=K+B=K+1 modulo B-1.

It follows that P is1 modulo B-1, so align is integral. We have N>=4 and
J>=B^(N-1)>N=K+B; hence P>B and align>0. All the quantities in (1) are
positive. In particular C<2B and q>=B^4 imply alpha>0. The precise native
marker equation holds:

    C=CS+Z+W.

The retained temporal alignment `(B-1)align=P-1`, repunit equation and
raw bound `C+alpha+d*x=q` all hold. The raw exponent has its exact required
value W=B^x; this is not an input-recoding example.

The transport is also exact:

    (K+P)C=JC=J((B-1)+c0)=(q-1)+F=F+z(q-1).            (2)

The selected period cannot divide q. J is odd and K is even, so P is an
odd integer greater than1, whereas q is a power of two. Thus no positive
v can satisfy the deleted equation P*v=q.

## 3. Both paid masks and the actual packed index

The word Z has only selector2 at its low cell and is accepted by MC*J.
Every digit of F is c0, which avoids MF. There are no carries: Z<B and
0<c0<B-1, giving 0<F<q-1. Consequently

    Z AND(MC*J)=0, F AND(MF*J)=0.

Put

    S=Z+qF, M=(MC+q*MF)J,
    r=(q^2-S)(q^2-1)+M.                                 (3)

The two fields are below q, so 0<S<q^2 and 0<M<q^2-1; their AND is zero.
In fact S<=q^2-q-1, so the retained bounds q^2<=r<q^4 hold. The inverse
packed-mask identity of the 80 proof applies with Lambda=q^2. The mask
population is dN, and therefore

    popcount(r)=2dN+dN=3dN.                              (4)

The index is odd: S is even, MC*J is odd, and the other terms contributing
to M are even. Equation (4) gives exactly the required divisibility by
the original scale D0=q^3. No weaker population threshold is used.

The apparent low cell of C has both Start selector1 and selector2, with
no copy bits. It is not a legal window cell. Nevertheless the unrelated
supplied field F passes its mask because the non-power period P prevents
the transport equation from being interpreted as aligned cyclic shifts.
That is the missing implication when P*v=q is removed.

## 4. Fresh positive kernel and input witnesses

The retained fixed-minus 43-operation kernel depends on q, r and its scale,
not on the missing period quotient. At this actual odd r, the explicit
bounds in Section3 and the exact population (4) satisfy the positive
converse used in the 80 proof. It supplies all seventeen fresh positive
kernel coordinates. None is reused from an unrelated packed example.

Write aP for that kernel's Pell parameter and Jindex=2r+1. The unchanged
input bridge has u=d*x=d, so 4<=u<q<Jindex and W=2^u. Its positive
witnesses are exactly

    kappa=psi_(aP+2)(u),       muP=chi_(aP+2)(u),
    delta=(kappa-u)/(aP+1),   phiP=c-kappa,
    rho=(muP-aP*kappa-W)/(4aP+3).

The retained Pell congruences make delta and rho integral. The inequalities
kappa>u and u<Jindex give delta>0 and phiP>0. Finally

    muP-aP*kappa=2*kappa-psi_(aP+2)(u-1)>kappa>W,

so rho>0 as well. All four input equations therefore hold at raw x=1.
Here kappa>W follows from kappa>=2(aP+2) and the kernel's bound
aP>2^(2r+1)>W.
Together with (1)--(3), this gives every one of the 32 positive witnesses
and all 20 equations of the weakened source. Since the fixed machine's
language is empty, it is a full arithmetic false positive.

## 5. Reproducible checks and their scope

The checker expands every weakened source residual, including the retained
acyclic norm correction, and verifies the exact 79-operation ledger. It
checks the empty machine's entire state-reachability graph and verifies
the two marked windows and a third allowed window, establishing k>=3
without enumerating the entire huge lifted alphabet.

The actual N=K+B is already too large to materialize as a computational
tableau exponent. Numerical examples therefore use explicitly labelled
surrogate constants with the same arithmetic hypotheses used in Sections
2--4. They verify all retained outer equations, both masks, exact raw
exponent, positive quantities, forbidden period divisor, odd packed index,
full population threshold and scale bounds. Their manageable N satisfies
the more general sufficient conditions

    N>=4, N=K+1 modulo B-1, J>K+B.

These numerical examples are not claimed to be the actual window-copy
compiler. The actual empty-machine instance is established parametrically
by Sections1--4, while the full kernel witnesses are proved positive and
are not numerically materialized. The sound 80-operation source is unchanged.

Review status: author and independent complete proof/source reviews pass.
Fresh verification matches the saved receipt. The default checker compares
its result with that receipt; only `--write` regenerates it.
