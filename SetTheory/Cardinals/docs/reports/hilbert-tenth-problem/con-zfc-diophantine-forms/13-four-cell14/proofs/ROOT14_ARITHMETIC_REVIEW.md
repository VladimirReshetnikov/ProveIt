# Independent arithmetic review of the fourteen-variable equations

This review concerns the emitted `root14_product75` and `root14_outer73`
circuits. It is independent of their circuit builder and uses the sparse
polynomial implementation in `quartic33.py`. It checks exact identities
and uniform highest homogeneous forms, without sampling or assuming the
equations themselves vanish.

## Formulas and reconstruction

Use the normalized fifteen-variable predecessor, and remove `f`. Put

    D=1+Delta i^2 c^4,
    Q=(Delta i c^2)^2,
    u=cT,
    b=c+RD,
    P=N_first N_main N_index N_transport,
    A=Q(Du^2+b^2-y^2)+y^2-1,
    B=2Qub.

The two new polynomials are

    Phi=P(A^2-DB^2+1)-1,
    Psi=(P(A+1)-1)^2-D(PB)^2.

All variables still supplied to these expressions are strictly positive,
but the intermediate integer R may have either sign away from zeros.
Nevertheless `D>c>0`, so `b` cannot vanish: otherwise `R=-c/D` would
be an integer strictly between -1 and 0. Thus `B` is nonzero everywhere
on the positive retained-coordinate domain.

At a zero of Phi, the integer `A^2-DB^2+1` is a unit. Since B is even,
that integer is 1 or 2 modulo 4, and so cannot be -1. Consequently
`A^2=DB^2` and P=1. The rational number `f=A/B` has square D and is
therefore an integer. Since D>0 it is nonzero. The normalized strong
equation holds by the definition of D.

At a zero of Psi, P cannot vanish, since P=0 would make Psi=1. The
rational number `f=(P(A+1)-1)/(PB)` likewise has square D and hence
is a nonzero integer. It satisfies `P(A+1-Bf)=1`.

For either construction put `E=f^2-D` and

    V=uf-b-RE = c(Tf-1)-Rf^2.

The exact identity

    QV^2-(Q-1)y^2-1
      = A-Bf + E Q[u^2-2Ruf+2Rb+R^2 E]

shows that, at the reconstructed square root, the auxiliary norm equals
`A+1-Bf`. Thus both reconstructed tuples solve the normalized parent
product equation. The parent signed-root theorem, reviewed separately in
`ROOT_ELIMINATION_INDEPENDENT_REVIEW.md`, implies f>0. This last semantic
step is essential: a rational-square argument alone does not fix the
sign of f.

Conversely, a positive normalized parent solution has f^2=D and
auxiliary norm 1, so A=Bf and P=1. Both Phi and Psi vanish. Hence the
root elimination is an equivalence in existence of positive solutions.

The auxiliary identity, and the cross-check

    Psi-P Phi=(P-1)(2PA-1),

are verified by exact sparse-integer-polynomial arithmetic. No zero-set
identity has been used to simplify the polynomial away from zeros.

## Uniform degree certificates

Let `q0=beta J`, `k=eta+zeta`, and

    W=w(q0-F-alpha)-z q0.

Here beta is the fixed positive coefficient B-1. The main-norm
cancellation is the exact polynomial identity

    (ac+X+gamma H)^2-(a^2+H)c^2
      = 2ac(X+gamma H)+(X+gamma H)^2-Hc^2.

Its leading form is `8 gamma a0^2 c0`, where
`a0=w s q0^4` and `c0=k s q0^3`, so its exact degree is 18.
Every other gate's highest homogeneous form is propagated directly;
there is no other cancellation of a candidate highest form.

The complete highest homogeneous form of Phi is

    8 gamma h i^12 k^27 w^21 s^48 q0^177 (q0-F)^4 W.

It has degree 293. In particular the coefficient of

    J^182 h gamma i^12 eta^27 w^21 s^48 z

is `-8 beta^182`, nonzero for every valid compiler coefficient slice.

The complete highest homogeneous form of Psi is

    64 gamma^2 h^2 i^12 k^30 w^26 s^56 q0^206 (q0-F)^4 W^2.

It has degree 342. The coefficient of

    J^212 h^2 gamma^2 i^12 eta^30 w^26 s^56 z^2

is `64 beta^212`, likewise uniformly nonzero. These are degree proofs
over the integers, stronger than a degree observation on one finite-field
line.

## Operation and dependency check

An independent walk of the two saved circuits finds:

| Circuit | Unknowns | Gates | Multiplications | Additions/subtractions | Exact degree |
|---|---:|---:|---:|---:|---:|
| Phi | 14 | 75 | 44 | 31 | 293 |
| Psi | 14 | 73 | 44 | 29 | 342 |

Every gate and every declared unknown/coefficient port reaches the final
output. Fixed constants are charged as degree zero; multiplication by
fixed constants, including small integers, is charged as a multiplication.

Run `python3 code/root14_independent_audit.py` to recompute and check
`data/root14_independent_checks.json`. Add `--write` to regenerate that
artifact. Both it and `quartic33.py` use explicit exceptions, so their
checks remain active under `python -O`.

The checks do not constitute a proof-assistant verification of the Pell
lemmas, the native compiler, or the K215 calibration; those remain the
ordinary mathematical dependencies stated elsewhere in the package.
