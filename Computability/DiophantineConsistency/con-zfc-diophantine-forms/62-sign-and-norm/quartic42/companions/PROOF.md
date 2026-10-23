# Sextic and octic companions of Q42

The two new packets are `sextic35.json` (35 unrestricted integer unknowns,
20 residuals of degree at most 3, exact sum-of-squares degree 6) and
`octic30.json` (30 unrestricted integer unknowns, 15 residuals of degree at
most 4, exact sum-of-squares degree 8). They use the **same entire source34
coefficient tuple** as Q42. Their correctness uses Q42's ordinary proof and
its expressly stated inherited compiler/calibration theorems; no additional
machine or universal-polynomial theorem is invoked here.

The polynomial equations and complete restoration maps are literal JSON.
All variables are integers. A fixed coefficient symbol is a bound integer,
not a quantified parameter. Every abbreviation below is a polynomial.

## Relocated square guard

Let Q42X be Q42 with the single residual

    q - 2*q_half_root^2

replaced by

    X - 8*rho^2.

The other 26 residuals, including `w=4*u^2`, are unchanged. This is the
packet `quartic42_x_square.json`.

**Lemma.** The integer zero sets of Q42 and Q42X are in bijection: keep
every other coordinate fixed and replace `q_half_root` by
`rho = u*q_half_root`. The inverse is `q_half_root = rho/u`.

**Proof.** We first show that `u` cannot be zero at a zero of either
system, without using either version of the square guard. The two retained
positive forms give `F*alpha>0` and `F*C>0`, where `C=q-F-alpha`. Thus
`F,alpha,C` have the same nonzero sign, and `q=F+alpha+C` has absolute value
at least 3. The first defining rows give `N=q^3`, `X=w*q`,
`a=E+(2*v_scale+1)*N`, and `E*(X+1)=X*a`. If `u=0`, then `w=X=E=0` and

    a = (2*v_scale+1)*q^3,
    |a| >= 27.

Put `H=4*a+3`. The main norm and its defining rows give

    D=a*c+gamma*H,
    Delta=a^2+4*a+3,
    D^2-Delta*c^2=1.

Modulo `H`, the left side is zero. Hence `H` divides 1, impossible because
`|H|>=105`. Therefore `u` is nonzero.

For a Q42X zero, its scale rows imply

    q*u^2 = 2*rho^2.

Write `rho/u=a0/b0` in lowest terms with `b0>0`. Then
`q*b0^2=2*a0^2`, so `b0^2` divides 2. Consequently `b0=1`, `u` divides
`rho`, and `q=2*(rho/u)^2`. This restores the exact deleted Q42 guard.
Conversely a Q42 zero satisfies
`X=w*q=4*u^2*2*q_half_root^2=8*(u*q_half_root)^2`, giving a Q42X zero.
The two maps are inverse because `u!=0`. QED.

The relocation keeps degree four and 42 variables. Its purpose is to
make `X` a quadratic expression independently of the cubic expression
`4*u^2*q`; this permits one more register elimination in the octic.

## General elimination fact

If one residual is exactly `v-f(other variables)`, or its negative, then
delete that residual and replace `v` by `f` in every other residual. The
remaining variables are unrestricted integers and `f` has integer
coefficients, so this gives a bijection between the two integer zero
sets. No divisibility hypothesis or positivity condition is needed. A
triangular coordinate change `t_old=t_new+g(other variables)` is likewise
an integral bijection.

`build_companions.py` checks each of the 19 eliminations used below by
exact sparse-polynomial equality, rather than merely propagating degrees.
It also directly substitutes each **complete final restoration** into all
27 Q42X residuals. Each is identically zero or exactly one of the final
residuals, and each final residual occurs once.

## The sextic in 35 integers

First make the integral coordinate change

    tau_old = tau_tail + P - eta - zeta.

Write `k=eta+zeta`. Eliminating `P=k+E*(c-eta)` changes the first norm to

    tau_tail^2 + (2*tau_tail-k)*E*(c-eta) - 1.

The quartic term cancels exactly. Next eliminate the following six
coordinates (the displayed order together with P is the checked order):

| Eliminated coordinate | Restoration |
| --- | --- |
| P | `eta+zeta+E*(c-eta)` |
| F2 | `f^2` |
| g | `y^2-V^2` |
| X | `8*rho^2` |
| N | `q*(L+1)` |
| C2 | `c^2` |
| w | `4*u^2` |

The old Pell root restores as `tau_old=tau_tail+E*(c-eta)`. There are
`42-7=35` variables and `27-7=20` residuals. The full factored list is in
`sextic35_readable.json` and in the report; the expanded exact residuals
are in `sextic35.json`. Every residual has degree at most 3. The row

    I-(2*r+1)*c^2

is the only row containing `r`. Thus the coefficient of `r^2*c^4` in the
sum of squared residuals is exactly 4. Its total degree is exactly 6,
including after specializing every fixed coefficient to the authentic
large integer.

## The octic in 30 integers

No change of the Pell-root coordinate is needed. Eliminate these twelve
registers in the checked order:

| Eliminated coordinate | Restoration at this elimination step |
| --- | --- |
| N | `q*(L+1)` |
| C2 | `c^2` |
| F2 | `f^2` |
| g | `y^2-V^2` |
| w | `4*u^2` |
| X | `8*rho^2` |
| zeta | `P-E*(c-eta)-eta` |
| Baux | `I^2` |
| D | `8*rho^2+a*c+gamma*(4*a+3)` |
| Delta | `a^2+4*a+3` |
| P | `1-V+j*c+h*E+E*(c-eta)` |
| L | `q^2-1` |

After composing these substitutions, the original sum `eta+zeta` is the
polynomial abbreviation

    k = 1-V+j*c+h*E,

and `zeta=k-eta`. This preserves the common-sign guard as
`eta*(k-eta)=Pos(EZ_pos1,EZ_pos2,EZ_pos3)`, a cubic equation. The full
factored list is in `octic30_readable.json`; the report and exact packet
give all 15 residuals. There are `42-12=30` variables. Each residual has
degree at most 4. In particular, the restored auxiliary norm is

    I^2-(a^2+4*a+3)*(f^2-1).

Its square contributes `a^4*f^4` with coefficient 1. No other residual
contains both `a` and `f`, so this coefficient remains exactly 1 in the
sum. The total degree is exactly 8 on the authentic coefficient slice.

## Formalizable conclusion and audit scope

The square-guard lemma and all substitutions use elementary integer
arithmetic formalizable in ZFC. Composing them with Q42's theorem gives

    ZFC proves: no integer zero of sextic35 iff Con(ZFC),
    ZFC proves: no integer zero of octic30 iff Con(ZFC).

Neither statement asserts that ZFC proves its own consistency. No proof
assistant certificate for these new literal polynomials is claimed.

Normal and optimized Python runs check the same explicit conditions;
no check is a removable `assert`. The audit proves literal polynomial
identities, dimensions, degrees, and coefficient certificates. It does not
replace the unbounded Pell/compiler proof. The historical collection
README lists 42-integer sextic and 36-integer octic packets (sources 27
and 29); the resulting reductions are 7 and 6 unrestricted integers,
respectively. These are comparisons to the supplied collection, with no
claim of global minimality or priority over all external work.
