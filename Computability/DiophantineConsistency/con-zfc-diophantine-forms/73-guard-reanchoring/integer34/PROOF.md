# A transport pivot and a reanchored sign guard

This contribution is a local exact reduction of the source64 integer
quartic41 at ProveIt commit
`9cca523d9f27ad39d52993f4065cbd7e58f8bdd4`.  It produces one polynomial
of exact degree six in **34 unrestricted integer unknowns**, compared with
the collection's existing degree-six equation in 35 integer unknowns.

The literal polynomial is defined by `sextic34.json`: square each of the
19 listed residuals and add them.  Its fixed coefficient ports are
precisely the source quartic41 tuple `(beta,K0,MC,MF)`.  In particular
`beta=2^1064921-1`, and `MF` already includes the source's mask shift.
The tuple must be used as a whole; this reduction does not support mixing
ports from other compiler generations.

## Statement

Let `Q41` be the pinned source quartic41 with this coefficient tuple, and
let `S34` be the sum of squares in `sextic34.json`.  Then

    (exists v in Z^41, Q41(v)=0)
      iff (exists w in Z^34, S34(w)=0).

The proof below is an arithmetic proof by polynomial identities and a
classical representation of positive integers.  Consequently any proved
source equivalence between zeros of Q41 and refutations of ZFC transfers
unchanged to S34.  This contribution does not independently prove the
inherited native compiler/refutation calibration, and it does not add an
end-to-end Lean or object-language ZFC certificate.

## The sign gadget

For unrestricted integers s,t,v write

    Pos(s,t,v) = s^2+t^2+v(v+1)+1.

Its values are positive because each summand preceding the final 1 is
nonnegative on integers.  Conversely every positive integer m has this
form.  Indeed, `4m-3` is positive and is 1 or 5 modulo 8, so Legendre's
three-square theorem writes it as a sum of three integer squares.
Reduction modulo 4 shows exactly one square is odd; permuting coordinates
and dividing the two even coordinates by 2 yields the required form.
Thus existentially quantified `Pos` witnesses express strict positivity.

For arbitrary integers F,alpha,C,

    F*alpha>0 and F*C>0
      iff C*alpha>0 and F*C>0.

Either pair says that all three entries have one common nonzero sign.
The associated positivity witnesses may have to be reselected.  This is
an existential equivalence, not a coordinatewise identity between the
two triples of witness values.

## Coordinate changes

Use `q=beta*J+1` and `k=eta+zeta`.  The original compiler complement is
`C=q-F-alpha`.  Replace the unknown alpha by the unknown C; the inverse
change is

    alpha=q-F-C.

Reanchor the first sign guard from `F*alpha=Pos(FA)` to
`C*alpha=Pos(CA)`, keeping `F*C=Pos(FC)`.  This costs no variable and
preserves the set of core coordinates admitting witnesses.

The source transport row is

    (K0+4*w_scale)*C - F - z*(q-1) = 0.

It is monic in F after the complement change.  Thus eliminate F by the
polynomial substitution

    F=(K0+4*w_scale)*C-z*(q-1).

This F has total unknown-degree at most two.  Reanchoring the first
guard was necessary for the degree bound: the resulting guards
`C*(q-F-C)` and `F*C` have degree at most three, whereas `F*(q-F-C)`
would have degree four.

Retain the independent unknown N and its cubic defining row `N-q^3`.
Eliminate six further source unknowns by their monic defining rows:

    L=q^2-1,       X=2*u^2,     C2=c^2,
    F2=f^2,       g=y^2-V^2,   P=k+E*(c-eta).

The literal source first norm is `tau^2-P*(P-k)-1=0`; using its defining row `P-k=E*(c-eta)` gives `tau^2-E*(c-eta)*P-1=0`.
Before substituting P, replace tau by the affine gap coordinate

    tau=tau_gap+E*(c-eta).

This invertible polynomial change turns the first norm into

    tau_gap^2+(2*tau_gap-k)*E*(c-eta)-1=0.

This is cubic; a direct substitution without the gap change would leave
a quartic term.

## The resulting 19 residuals

The definitions and ordered unknown list are in the literal JSON.  In
the following expressions F and q are the polynomial abbreviations just
given, H=4a+3, and k=eta+zeta:

    N-q^3
    2u^2-4*w_scale*q
    a-E-(2*v_scale+1)N
    2u^2(E-a)+E
    c-eta+(E-a)k
    tau_gap^2+(2*tau_gap-k)E(c-eta)-1
    D-2u^2-ac-gamma*H
    Delta-a^2-4a-3
    D^2-Delta*c^2-1
    k-1-hE-[(q-F)(N-q)-C(q^2-1)+(MC+qMF)J]
    V+c-fo
    -Eh+V-cj+k-1
    I-(2r+1)c^2
    Baux-I^2
    Baux-Delta(f^2-1)
    Baux(V^2-y^2)+y^2-1
    C(q-F-C)-Pos(CA_pos1,CA_pos2,CA_pos3)
    FC-Pos(FC_pos1,FC_pos2,FC_pos3)
    eta*zeta-Pos(eta_zeta_pos1,eta_zeta_pos2,eta_zeta_pos3).

The packed row is cubic because N remains an unknown of degree one;
its equality to q cubed is enforced by a separate row.  The identity
behind its displayed form is

    ((q-1)(q-F)+alpha)(q^2-1)
      = (q-F)(q^3-q)-C(q^2-1),

under `alpha=q-F-C` and `N=q^3`.

## Both directions

From a source Q41 zero, reselect the first positivity triple for
`C*alpha>0`, set `C=q-F-alpha`, and set
`tau_gap=tau-E*(c-eta)`.  The seven eliminated rows force the stated
polynomial substitutions, and the remaining 19 rows give a zero of S34.

Conversely, a zero of S34 makes every listed residual zero, because all
residuals are integers and the polynomial is their sum of squares.
Restore alpha,F,L,X,C2,F2,g,P,tau using the displayed substitutions.
The guard equations imply `C*alpha>0` and `F*C>0`, hence
`F*alpha>0`; choose a fresh source FA positivity triple.  The restored
coordinates satisfy every one of the 26 source residuals.  Thus the
restored source tuple is a zero of Q41.

## Dimension and exact degree

The complement and tau changes preserve the number of unknowns.  The
transport pivot eliminates F, and the six remaining monic substitutions
eliminate L,X,C2,F2,g,P.  Therefore the number of unknowns is
`41-7=34`; the number of residuals is `26-7=19`.  Every remaining
unknown occurs in the polynomial.

All 19 residuals have degree at most three, so their sum of squares has
degree at most six.  Only the residual `I-(2r+1)c^2` involves r, and
its square has coefficient 4 on `r^2*c^4`.  Thus that coefficient in
the full polynomial is exactly 4, proving that the degree is exactly
six without relying on numerical values of the coefficient ports.

## Reproducible checks

Run

    python3 build_sextic34.py
    python3 verify_sextic34.py

The second program does not import the first.  It parses the separately
stored literal source and result into its own exact sparse polynomial
ring over the integers, authenticates the source Git blob, checks all
26 restoration identities, checks the inverse affine identities,
computes the exact residual degrees, and expands the complete sum of
squares.  It writes `VERIFICATION.json` and `sextic34_expanded.json`.
For the literal circuit its expansion has 437 monomials when the four
fixed coefficient ports are treated as independent symbols.  It also
checks all 27 sign cases; the preceding common-sign argument supplies
the unrestricted-integer proof.

The source Git blob is `521f16a310f49e736ea8ffac3fe13847ff71adcb`.
The program's finite checks certify the local algebra and metrics.
They do not decide consistency or replace the inherited compiler proof.
