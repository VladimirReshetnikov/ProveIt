# Exact circuit compression of the twelve-positive-variable norm

## Scope and source

Pinned repository: `VladimirReshetnikov/ProveIt`, commit
`8c6eec9d19ef80538c8e61ff6e0180040583446a`.
Paths below are relative to
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms`.

The source is package `30-quartic31/positive/`: its `positive12_system.json`,
`POSITIVE12_PROOF.md`, and `build_positive.py`. This note proves exact polynomial
identity in the four symbolic coefficient ports, not merely equality of zero
sets, for the compressed product. The active fixed instance is then rebound as
a whole to the new 121 by 8801 tuple using the coefficient adapter theorem.
The transport shift is the existing shift of
`26-ratio12/proofs/RATIO12_PROOF.md`, Section 8, applied after that exact refactor.

| Presentation | Positive unknowns | Equations | Exact degree | Operations |
|---|---:|---:|---:|---:|
| Package 30 product | 12 | 1 | 1081 | 111 |
| Refactored product | 12 | 1 | 1081 | **108** |
| Package 30 system | 12 | 3 | 7, 2, 1072 | 107 |
| Refactored system | 12 | 3 | 7, 2, 1072 | **103** |
| Refactored and shifted system | 12 | 3 | 7, 2, 1072 | **102** |

Every binary addition, subtraction and multiplication, including by a fixed
constant, is charged. Comparison is free. Polynomial abbreviations are not
additional unknowns. The twelve supplied unknowns are strictly positive integers.
For the shifted system, the supplied z equals the original z minus one.

All four active coefficient ports use the **whole new 121 by 8801 Wang943 tuple**.
`COEFFICIENT_BINDING.json` refers to the exact payloads in `../coefficients/payloads`
and to the complete proof in `../coefficients/COEFFICIENT_PROOF.md`. The aliases
are beta=beta, K0=K, MC=MC, and MF=MF_source. The last is already shifted by B-1.
The historical tuple embedded in `upstream/positive12_system.json` is retained as
source evidence; it is not the active tuple. The code does not claim that four
arbitrary numeric ports instantiate the semantic compiler.

The upstream evidence files have been restored to exact source bytes and checked
against their Git blob identifiers. `SOURCE_PINS.json` records this authentication;
the working download copies had one extra terminal newline, which has been removed.

## Explicit definition

Let the twelve supplied positive integers be
`J,F,alpha,z,h,i,T,s,w,eta,zeta,t`. Use the source's fixed integers
`beta,K0,MC,MF` and set

    q=beta*J+1, Cw=q-F-alpha, X=w*q, Y=s*q^3, E=X*Y,
    k=eta+zeta, c=k*Y+eta, a=E+Y, H=4*a+3,
    Delta=a^2+H, ell=E*k*Y,
    A=1+ell*(ell+k), G=1+Delta*c^2, b0=X+a*c,
    R=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J,
    Nk=k-h*E-R, Nt=(K0+w)*Cw+q-F-z*(q-1),
    I=i*c^2, D=1+Delta*I^2, Q=Delta*(D-1), d=Q-1,
    b=c+R*D, M=k*(I^2+T^2), L=H*M+1, W=b0+H*t.

The remaining polynomial registers are

    S=H^2*Q,
    HP=S*D*c^2*T^2, HU=S*b^2,
    n=(H*M)^2*A, dn=d*n, He=HP+HU-H^2, j=4*HP*HU,
    Tr=2*d*(W^2+L^2*G), r=d*(W^2-L^2*G), K=r^2,
    a1=Tr-2*(dn+He), b1=(dn-He)^2-j-K,
    v=a1*(a1*Tr+2*b1)-16*dn*j,
    u=a1^2*K-b1^2,
    Rnorm=K*v^2, Lnorm=u*(Tr*v-u), N=Rnorm-Lnorm.

The product equation is

    Nk*Nt*(1+N)-1=0.

The unshifted system is

    Nk=1, Nt=1, Rnorm=Lnorm.

The shifted system is

    Nk=1, (K0+w)*Cw=F+z*(q-1), Rnorm=Lnorm.

These are explicit ordinary polynomials: the source lists in the three generated
JSON packets evaluate them using only binary +, -, and multiplication. In
particular no radical or rational-function primitive is part of the circuit.

## Four exact arithmetic simplifications

First, the source computes `P=Q*D*c^2*T^2` and `U=Q*b^2`, and later multiplies
each by `H^2`. Instead share `S=H^2*Q`. Both resulting registers HP and HU
are exactly unchanged in every commutative ring, and one multiplication is saved.

Second, the source computes `K=d^2*(W^2-L^2*G)^2`. Computing
`r=d*(W^2-L^2*G)` and then `K=r^2` saves one multiplication, because the source
has no other use of the intermediate `d^2`.

Third, the source's final two quadratic-remainder coefficients are

    vr=a1*(a1*Tr+2*b1)-16*dn*j,
    ur=b1^2-a1^2*K.

Its norm is `ur^2+Tr*ur*vr+K*vr^2`. Set `u=-ur` and `v=vr`. The ring identity

    ur^2+Tr*ur*vr+K*vr^2 = K*v^2-u*(Tr*v-u)

both reverses an existing subtraction and factors a common term. It needs six
operations at the final stage instead of seven, saving a third multiplication.
Therefore the **product is literally the same polynomial template in the four
ports** as the source's degree-1081 product, now evaluated in 108 operations.
For the historical tuple it is the same fixed polynomial. The delivered active
polynomial uses the new complete tuple and is a different fixed specialization.
Universal soundness and completeness transfer through the coefficient adapter;
the source parity argument and exact-degree proof are unchanged. No new
algebraic-number or Pell argument is needed for the circuit refactor.

Fourth, the system compares the last two terms directly, omitting their final
subtraction. This saves one additional operation, giving 103 operations for
the three-equation system. The defining residual is still exactly N, so its
exact residual degree remains 1072, even if individual comparison terms are
regarded as separate circuit outputs.

## The positive transport shift

Replacing `z_old` by `z+1` in the original equation `Nt=1` gives the exact identity

    (K0+w)*Cw+q-F-(z+1)*(q-1)-1
      = (K0+w)*Cw-F-z*(q-1).

The new comparison takes four arithmetic operations instead of five. Thus the
shifted system has 102 operations.

Soundness needs no additional premise: every positive shifted solution gives a
positive unshifted solution by taking `z_old=z+1`. For completeness, first
recover the authentic blank compiler from an unshifted solution. The inherited
compiler then gives `Cw>0`, `q>F`, `X=w*q=2^R`, and `R>3q`, so `w>q>F`.
The transport equation gives

    (z_old-1)*(q-1)=(K0+w)*Cw-F>0.

Since `q>1`, it follows that `z_old>=2`, so `z=z_old-1` is positive. This is the
existing positive transport shift, with its semantic hypotheses used only after
the unshifted reconstruction. No stronger bound is assumed in the bootstrap.

## Logical theorem

By the pinned package-30 theorem and the complete new coefficient adapter, the
active positive system and product have a solution if and only if the literal
blank K215 machine halts, if and only if there is a finite syntactic ZFC refutation.
The exact port-parametric identities above preserve the first system and polynomial;
the proved positive coordinate shift preserves existence. Consequently ordinary
mathematics formalizable in ZFC proves, for each new presentation,

    (there is no solution in strictly positive integers) iff Con(ZFC).

This is a small circuit improvement. It is not a new minimal-variable theorem,
not an improvement on the separate 67-operation equation using more unknowns,
not a global optimum, and not a new end-to-end proof-assistant formalization.

## Reproduction and validation

Run

    python3 build_refactored12.py
    python3 check_refactored12.py

The builder emits literal circuits with complete gate accounting. The checker
uses a separate sparse-polynomial implementation to establish five local ring
identities exactly. It also verifies graph liveness and the ledgers, and compares
240 signed modular assignments with the pinned source circuit, including the
transport-coordinate shift. It authenticates all four actual active payloads
and checks twelve additional assignments at their residues. Assertions are not
used as validation gates, so the checker retains its checks under `python3 -O`.

The small symbolic identities prove the algebraic rewrites universally. Modular
evaluations are transcription diagnostics. Neither kind of finite check replaces
the inherited semantic compiler, proves that a K215 refutation witness exists,
or decides consistency.
