# Exact degree floor for the fixed scalar frame

## Statement and scope

Keep **all** Round 18 free-scale scalar registers, authentic coefficient ports,
and eleven independent coordinates fixed. Let `L` be any nonzero integer, and
let `Psi` be any integer polynomial in the ten coordinates other than `n`.
Set

    Z=S(n+Psi)-Ac,
    pa=delta Z^2,  pb=delta S^2 P,
    pc=L^2 S^2 B Df Cy,
    N=(pa+pb-pc)^2-4pa pb.

Then the total degree of `N` is at least **300**. Round 18's `L=32`,
`Psi=Psi_300` attains 300. Thus 300 is the exact minimum in this fixed-frame,
constant-weight, integer-center family.

This is not a bound for arbitrary eleven-variable consistency equations,
different carriers, different auxiliary norms, polynomial weights, coordinate
changes of the other ten variables, or different polynomial encodings. Even
weights are required for the retained logical equivalence theorem; the
degree statement itself holds for every fixed nonzero integer weight.

## Exact highest homogeneous forms

A subscript `0` denotes the full highest homogeneous component, not a
lexicographically chosen monomial. All six authentic numerical ports have
degree zero. With the exact positive numeral `beta=2^1064921-1`, write

    q0=6 beta j,             W0=12 w,
    X0=q0 W0,               a0=X0 v,
    F0=W0 C-z q0,           k0=R0=-q0^3 F0,
    ell0=X0 v^2.

The sums `F0` and `k0` are nonzero homogeneous polynomials. Their degrees are
respectively 2 and 5; `q0,X0,a0,ell0` have degrees 1,2,3,4.
Directly from the literal register definitions,

| Register | Degree | Highest homogeneous component |
|---|---:|---|
| A | 3 | a0 |
| Delta | 6 | a0^2 |
| Dm | 8 | a0^2 c^2 |
| B | 12 | r a0^3 c^2 |
| U | 11 | r a0^2 c^4 |
| Df | 22 | r a0^5 c^6 |
| Q, delta | 28 | qstar = r a0^7 c^6 |
| V | 37 | vstar = 4 r^2 a0^8 c^10 T |
| Cy | 102 | qstar vstar^2 |
| Dt | 18 | ell0^2 k0^2 |
| Budget | 18 | -k0^2 q0^8 |
| P | 56 | -pstar^2, where pstar=q0^4 ell0^2 k0^3 s |
| S | 20 | sstar=128 s r a0 q0^15 |

For the budget, the negative term `-k^2 q^8` has degree 18, while the other
two terms `Y^2 k^2(q^2-Derr)` and `-4Y^2 q^2 eta^2` have degree at most 16.
Thus its degree-18 part is exactly the displayed negative square.
Since `P=Dt+(Budget-4)Dt^2 s^2`, the stated degree-56 negative square follows
without any hidden cancellation. This sign is the decisive invariant.

For completeness, `H0=4a0`, `M0=2q0^3`, and the carrier's highest component is

    zc0=8 a0 q0^3 T-4 q0^3 X0^2,
    Ac0=zc0^5,                         deg Ac=35.

Every listed highest component is nonzero in the actual polynomial ring:
the variables are independent and `beta` is the fixed nonzero numeral.

## Degree proof

Let `d=deg Psi`, with the zero polynomial treated separately as `d=-infinity`.

If `d<54`, then `deg Z<=73`, `deg pa<=174`, whereas `deg pb=124` and
`deg pc=176`. Thus `H=pa+pb-pc` has degree 176. The cross product has
degree at most 298, so `deg N=352`.

If `d>54`, then `deg Z=20+d` and `deg pa=68+2d>176`; this dominates both
`pb` and `pc`. Consequently

    deg N=2 deg pa=136+4d>352,

because `deg(4pa pb)=192+2d` is strictly lower.

It remains to consider `d=54`. Let `psi0` be the nonzero degree-54
homogeneous part of `Psi`. Then

    pa0=qstar sstar^2 psi0^2,
    pb0=-qstar sstar^2 pstar^2,
    (-4pa pb)_0=(2 qstar sstar^2 psi0 pstar)^2.

The last expression is a **nonzero square** of degree 300. Put `h=deg H`.
If `h<150`, the cross term alone gives degree 300. If `h>150`, `H^2`
has larger degree and gives `2h>300`. If `h=150`, the degree-300 component is

    H0^2+(2 qstar sstar^2 psi0 pstar)^2.

It is nonzero: a sum of two real polynomial squares, one of them nonzero,
cannot vanish identically. Hence in every case

    deg N=max(2h,300)>=300.

This proof neither assumes a zero nor assumes the inherited consistency
calibration. It concerns the literal polynomial for the actual fixed ports.
The existing complete Round 18 center-remainder calculation supplies the
attaining center and its uncancelled degree-300 coefficient.
