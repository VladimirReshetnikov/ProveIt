# Maintained-carrier internal power recovery: proposed next checkpoint

Status: source/math proposal only. No new proof source, private overlay,
compiler invocation, dependency refresh, or accepted-source edit accompanies
this plan. The FirstIndex author bytes remain frozen. The exact cache inventory
will select its independently accepted ROOT provider after that provider is
published; no pending author object is silently called accepted.

## Requested leaf and exact public target

Propose `ArithmeticPellPowerRecovery.lean` and focused Checks, with the sole
import `DiophantineConsistency.ArithmeticPellFirstIndex`. Work uniformly in
`V` with `ORingStructure V` and `V` a model of `IΣ1`. Write
`X_t(b)=ArithmeticPellRecurrence.xcoord t b`, `Y_t(b)=...ycoord t b`,
`D_b=(b+1)(b+3)` and `E(t)=Exp.exp t`, using the instance constructed in
`LO.FirstOrder.Arithmetic`. Here `E(t)` is the represented **base-two** exponential
at an arbitrary internal index, not external natural exponentiation. The
literal carrier scale called E in FirstIndex is denoted `E0` below.

The final `maintained_power` signature copies the complete literal inputs of
`ArithmeticPellFirstIndex.maintained_first_indices`, strengthening only
`0<beta` to `15≤beta`. Its scalar ports are natural model elements
`beta,K,MC,MF`; require `MC<beta` and `MF<2*beta`. Require strict positivity
of every one of the fourteen variables, in the existing order:
`J,F,alpha,z,f,i,T,s,w,N,eta,zeta,y,gamma`.

Use these exact lets, with justified natural subtraction inherited from
FirstIndex where needed:

```
q = beta*J+1             X = w*q             Y = s*q^3
E0 = X*Y                k = eta+zeta        c = k*Y+eta
a = E0+Y                H = 4*a+3          d = X+a*c+gamma*H
R = ((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J
tau = E0*N+k-R          I = D_a*i*c*c
u = absdiff(f*f*c*T, f*f*R+c)
```

The five equation inputs are exactly:

```
(K+w)*q+q = (K+w)*(F+alpha)+F+z*(q-1)+1
 tau*tau = 1+(E0*Y)*(E0*Y+1)*k*k
     d*d = 1+D_a*c*c
     f*f = 1+D_a*(i*c*c)*(i*c*c)
 I*I*u*u+y*y = 1+I*I*y*y
```

The target is `X = Exp.exp R ∧ Exponential R X ∧ Exp.exp R < Y`.
No source-row package, source validity, desired first/main index, oddness,
rank window, large ordinate, half-window, power identity, or existence of a
cofinal canonical witness occurs among the premises. There is no additional
positivity premise on a signed auxiliary coordinate: the exact FirstIndex
`absdiff` input is retained. K, MC and MF may be zero subject to the stated
bounds; they are nonnegative because they are elements of natural arithmetic.
T and gamma retain the existing positive-variable domain.

## Derive the classified coordinates, do not assume them

Invoke accepted `maintained_first_indices` on the five inputs. It derives
`n≥5`, `2*n=R+1`,

```
k = 2*Y_n(B),       c = Y_R(a),       d = X_R(a),
B = 2*(X*Y^2-1)+1,  a = Y*(X+1).
```

The equalities `E0*Y=X*Y^2` and `a=Y*(X+1)` are ring identities.
Since n≥5, let r=n-1 and justify r+1=n; then r≥4 and R=2*r+1.
The first base is exactly the existing B, with
`B+2=2*X*Y^2+1`, justified by `1≤X*Y^2`.
No replacement of the doubled first coordinate by an undoubled one occurs.
Also beta≥15, J≥1 and w≥1 give q≥16 and X≥16; s≥1 gives Y≥1.
Finally eta<eta+zeta=k since zeta>0, hence
`c=k*Y+eta < k*(Y+1)`. These are all the extra inputs to the comparison below.

## Smaller internal comparison, avoiding arbitrary-base powers

The external guide NativePellPower uses a cross-product ratio and powers
`X^r`. They need not be internalized. Only the existing base-two exponential
is needed, with a constant factor sixteen at each paired recurrence step.

First derive directly from `ArithmeticPellRecurrence.norm`:

1. `(b+1)*Y_t(b) < X_t(b)` for every t, including zero, since
   `X_t^2 = ((b+1)*Y_t)^2 + 1 + 2*(b+1)*Y_t^2`.
2. `X_t(b) ≤ (b+2)*Y_t(b)` for t>0. Indeed `time_le_y` implies
   `1≤Y_t`, so `X_t^2=1+D_b*Y_t^2≤(1+D_b)*Y_t^2`.

The square comparisons are in the nonnegative ordered semiring. Then actual
`y_succ` gives

```
(2*b+3)*Y_t(b) < Y_(t+1)(b)                 (all t),
Y_(t+1)(b) ≤ 2*(b+2)*Y_t(b)                (t>0).
```

Retain the positive-time restriction on the upper bound: it is false at t=0.
The lower bound remains strict there, since Y_0=0 and Y_1=1.

Put `A=a+2`, `P=B+2=2*X*Y^2+1`, `L=2*a+3`, `U=2*P`.
For X≥16 and Y≥1 the explicit polynomial comparison is

```
L^2 = 4*Y^2*(X+1)^2 + 12*Y*(X+1) + 9
    ≥ 64*X*Y^2 + 204 + 9
    > 64*X*Y^2 + 32 = 16*U.
```

Here `16*X≤X^2≤(X+1)^2` and `12*Y*(X+1)≥204`; no division,
analytic estimates, squarefree decomposition, or general exponent graph is used.

For internal r define `C_r=Y_(2*r+1)(a)` and `K_r=Y_(r+1)(B)`.
Both indices are positive. The two-step lower estimate and one-step upper
estimate give `C_(r+1)>L^2*C_r` and `K_(r+1)≤U*K_r`.
A genuine Sigma1 successor induction proves the non-strict invariant

```
Exp.exp(4*r)*K_r ≤ C_r.
```

The zero case is equality 1=1, not a spurious strict assertion. At a successor,
combine the two recurrence bounds with `L^2>16*U` and the induction hypothesis;
`Exp.exp(4*(r+1))=16*Exp.exp(4*r)` follows by four uses of `exp_succ`
(or the already imported `exp_add`). This also proves the strict version at
every positive r by applying the successor step after `zero_or_succ`.
Its induction predicate uses represented Pell functions and represented exp;
all parameters and indices are internal, and no standard-Nat induction on r is used.

For the derived r≥4, actual k=2*K_r and c=C_r therefore give

```
Exp.exp(4*r)*k < 2*c < 2*k*(Y+1),
Exp.exp(4*r) < 2*(Y+1).
```

The cancellation is by k>0. For r≥2, `2*r+3≤4*r`; monotonicity and two
successor equations yield

```
2*Exp.exp(2*r+1)+2 ≤ 4*Exp.exp(2*r+1)
                 = Exp.exp(2*r+3) ≤ Exp.exp(4*r).
```

Use `1≤Exp.exp(2*r+1)` for the first inequality. Together with the strict
upper bound, addition and multiplication cancellation give `Exp.exp R<Y`.
The small r=0,1 regimes and X<16 are irrelevant to the final literal client;
they are not claimed by the stronger comparison or smuggled in as axioms.

## Positive quotient projection and exact recovery

A second genuine Sigma1 induction proves, for every internal a,t,

```
∃ z, X_t(a) = Exp.exp t + a*Y_t(a) + (4*a+3)*z.
```

The initial witness is zero. If z is the current witness, the successor
witness is `Y_t(a)+2*z`: expanding `x_succ`, `y_succ` and `exp_succ`
verifies the equality using only `D_a=a^2+4*a+3`.
This keeps a nonnegative quotient, so no internal signed-number encoding,
modular inverse or external `χ_modEq_pow` theorem is needed.

At t=R, the literal definition of d and FirstIndex's d=X_R(a),c=Y_R(a)
therefore imply, after cancelling the common a*c,
`X+gamma*H=Exp.exp R+H*z`. Reduce this equality modulo positive H.
Both residues are canonical: X<a follows from Y≥1 and a=Y*(X+1), while
`Exp.exp R<Y≤a<H`. Thus X=Exp.exp R. `exponential_exp R` gives the
second conjunct `Exponential R X`. The quotient lemma itself covers t=0
and a=0; the final literal client has its derived large positive rank.

## Source binding and remaining obligations

The four ports remain `[beta,K,MC,MF_source]`. CurrentMaskData2011 defines
radix=2^47, width=47*2011=94517, beta=radix^2011-1, and
`ports K = ![beta,K,lowPort,highPort+beta]`.
MF in this proposal is already `highPort+beta`; do not add beta again.
The displayed polynomial/core conventions are Carrier65.core, including its
independent positive y, its first carrier `E0*N+k-R`, and scaled auxiliary
coefficient `delta*i*c^2`. The proposal neither changes the tuple nor uses
historical compact44 coefficients.

CurrentCarrierArithmetic2011.beta_ge_thirty_one/portBounds externally certify
a stronger beta bound and the full masks. These are source references only,
not imported internal proof oracles. Later internal constant certification
must establish beta≥15 and the two mask inequalities for these exact closed
ports. This is modest constant work, distinct from recovering X at arbitrary
nonstandard rank. Translating an actual positive polynomial zero into the five
additive equations remains a separate actual-syntax obligation. Conversely,
constructing simultaneous cofinal witnesses and deriving a PA/HA or final
consistency endpoint remain separate; this one-direction implication supplies
none of them.

## Existing API and proposed validation boundary

Existing FirstIndex returns both exact indices and the required large/half
bounds from the literal equations. Recurrence supplies norm/x_succ/y_succ,
time_le_y and the represented coordinate graphs. Foundation
`Exponential/Exp.lean` supplies range_exists_unique, exponential_exp,
exp_defined_deltaZero, exp_zero, exp_succ, one_le_exp, exp_pos and
exp_monotone_le. Its explicit IΣ1 totality proof is already in the accepted
closure. `Exponential/Log.lean` supplies exp_add and is also already present.
The external NativePellPower and PellRatio90 files are guides only.

Expected prospective cache: existing FirstIndex's exact108-module input DAG
plus the accepted FirstIndex main, hence109 custom modules,95 Foundation,
394 custom artifacts,38 external names with114 total boundary artifacts
(38 primaries+76 companions),508 first providers, zero refresh. This is an
expected count until the separate complete auditor authenticates the accepted
ROOT FirstIndex packet, all current source/header pins and all actual providers.
Only the proposed two fresh leaves would compile after ROOT reviews the plan;
there is no Foundation or package rebuild. Preserve M6000/j1/async=false,
512MiB reserve and every failed attempt with both input snapshots. Focused
checks should cover the t=0 quotient and comparison equality, strict comparison
only for positive r, the positive-time upper bound, and the full literal
endpoint with no source/index/power premise. All axiom reports must retain the
standard accepted logical axioms only.

Scoped arithmetic challenge: controller_certificate checked the recurrence
comparison and final discreteness. Its initial difference polynomial used
16P instead of16U; the correction was explicitly acknowledged. The actual
difference is `4*Y^2*(X^2-14*X+1)+12*Y*(X+1)-23`, and the bound displayed
above already uses the correct16U. This was a brief arithmetic challenge,
not source/provenance acceptance or a compiler replay.
