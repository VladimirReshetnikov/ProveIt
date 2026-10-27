# Proposed thirteen-variable, 178-operation, degree-86 tradeoff

This is a research proposal, not an accepted equation packet. No Lean source,
new coefficient tuple, maintained display, or complete candidate auditor has
been produced. The complete paid exploratory schedule and bounded leading-layer
checks support the proposed metric. A full per-gate audit and a fresh Lean
zero-set proof remain required before acceptance. The previously committed
third-search probes are preserved as exploratory history.

## Exact parent and notation

The parent is the accepted 97-operation degree-88 graph
`../thirteen-second-first-norm-corrections/polynomial88.json`, SHA-256
`32d896933d3f3a524adfad130bacddd5cb137bfe9438e62dfcfec570a8c0e8e1`.
Its thirteen strictly positive integer coordinates remain
`J,F,alpha,f,i,T,s,w,n,eta,zeta,m,gamma`; its fixed ports are the complete
current 2011 tuple `beta,K0,MC,MF`. In particular MF is the once-shifted source
port, and the tuple has 47,313 uncompressed bytes. No historical 2501 ports
are substituted.

Use the parent's exact polynomial blocks, with its `qm` written b, its `B`
written G, its `N0,N1,Na` written P,Q,U, and its `R` written R:

    b = beta*J; q = b+1; X = w*q; Y = s*q^3; E = X*Y;
    k = eta+zeta; K = k*Y; ell = E*K; c = K+eta;
    a = E+Y; H = 4*a+3; delta = a^2+H;
    Q = (X+a*c+gamma*H)^2 - delta*c^2;
    P = (E*n+k-R)^2 - ell*(ell+k);
    C = q-F-alpha; G = (K0+w)*C-F;
    V = f^2*(c*T-R)-c;
    y = 1+4*(b*(m-(c*T-R)*V*G)-G);
    U = delta*(f^2-1)*(V^2-y^2)+y^2;
    Z = f^2-delta*(b*i*c^2)^2.

Here R is exactly the parent's scalar rank polynomial, with all four ports.
Let A88 be the already paid parent correction coefficient:

    A88 = 16*T^2*V * ((b*G)^2*V*(f^2-1)
           + 2*f^2*(V*C*(2*b*G-X*C)-(b*G)^2*f^2*R)).

Thus the old corrected auxiliary is U88 = U-A88*(P-1).

## New coefficients and polynomial

All definitions below are integer polynomials. No variable or coefficient is
inverted. Write

    A = k-4*gamma;
    S = 8*gamma*(P-1)+K*(Q-1);
    Gc = K0*C-F; g = k*s*q^2;
    u = X*R; v = T*K; e = u-v; h = G-q*Gc = w*C-b*Gc;

and define the two compact coefficient brackets

    L1 = C*e*(2*X*v+f^2*(3*u-v))
         + 2*f^2*T^2*C*X*(K*X*eta+g^2)
         - 4*f^2*Gc*v^2;

    L2 = C*K*X*u
         + h*(-2*v*e+f^2*(R*(4*v-3*u)-2*T*v*X*eta))
         + f^2*T*v*g*(2*Gc-C);

    Bcorr = 16*(f^2*T)^2*C*(L1+2*L2);
    Hcorr = 8*b*f^2*(f^2*T)^2*v^2*Gc*(b*Gc+C);
    Uc = A*(U-(A88+Bcorr)*(P-1))-Hcorr*S.

The proposed equation is

    (P*Q-1)^2 + (Z-1)^2 + (Uc-A)^2 = 0.                 (★)

This is deliberately a residual sum of squares. Substituting A*U into the old
unit sphere would be invalid unless A=1; no such assertion is made here.
The old three-square unit sphere and (★) are generally different polynomials.

## Conditional positivity of the scale

This argument uses only positive coordinates, beta>0, and Q=1. It does not
use P=1, U=1, Z=1, a native word, or a Pell witness construction.

Since b is a positive integer, q>=2, X=w*q>=2, and Y=s*q^3>=8.
Also k=eta+zeta>eta>0, gamma>0, c=k*Y+eta>0, a=(X+1)*Y>0,
and H=4*a+3>0.
Suppose A<=0, so k<=4*gamma. Then

    c = k*Y+eta < k*(Y+1) <= 4*gamma*(Y+1) <= 2*gamma*a.

The last inequality is equivalent to 2<= (X-1)*Y, which follows already
from X>=2 and Y>=2. Expanding the actual main norm gives the exact identity

    Q = (X+gamma*H)^2 + 2*a*c*X + H*c*(2*a*gamma-c).

Every summand is nonnegative and the first is at least 4; indeed the final
two summands are positive. Thus Q>1, contradicting Q=1. Consequently

    Q=1 ==> A>0,

so cancellation of A is justified only after independently recovering Q=1.
There is no global positivity assumption on A in the polynomial definition.

## Whole positive zero-set equivalence

The source-bound accepted lemmas used here are:

* `ThirteenCorrectedStrong.first_ne_neg_one p v hb hv`: P is not -1 on
  the positive domain, with beta>0.
* `ThirteenUnitSphere96.main_ne_neg_one p v`: Q is not -1 unconditionally.
* `ThirteenUnitSphere96.positive_zero_iff_residuals p v hb hv`: the old
  75-operation sphere vanishes iff P*Q=1, U=1, and Z=1.
* Its proof obtains Z=1 first using `strong_ne_neg_one`; only then does it
  invoke `auxiliary_ne_neg_one p v hs`, whose explicit premise is Z=1.
  That premise turns delta*(f^2-1) into a square and invokes
  `ShortSystem.square_aux_ne_neg_one`. This proposal uses that exact
  conditional result, not an unproved unconditional sign of U.
* `ThirteenSecondFirstNormCorrections.positive_zero_iff75 true p v hb hv`
  identifies the complete positive zero set of the 97/88 parent with that
  75-operation sphere, with identical thirteen coordinates.

From (★), each integer square is nonnegative, hence P*Q=1, Z=1, and Uc=A.
An integer product equal to 1 has unit factors. The first two exclusions
therefore give P=Q=1, independently of Uc. Both ideal corrections then vanish,
so Uc=A*U. The preceding conditional scale lemma yields A>0, hence U=1.
The accepted residual characterization gives an old sphere zero, and the
accepted parent equivalence gives a 97/88 zero with the SAME coordinates.

Conversely, a 97/88 zero gives an old sphere zero and thus P*Q=1, U=1, Z=1.
Again the independent negative-unit exclusions give P=Q=1. Consequently
S=0, Uc=A*U=A, and every residual in (★) vanishes. This direction does not
need to assume or prove A>0 separately.

Thus both maps are the identity on all thirteen positive coordinates. No
canonical-only argument, sign assertion about V, signed-ordinate positivity,
extra native premise, or supplied target zero is used. A future Lean leaf
can inherit the exact current external ConZFC endpoint from the accepted
parent after this whole-zero-set theorem. This is not an internal HA, PA,
or ZFC proof and does not close the open HA calibration work.

## Paid schedule and degree evidence

`paid_lift_shared_probe.py` retains the parent's first 88 literal operations
through `Pminus1`, then pays 90 new operations, including all correction
coefficients, constant multiplications, residuals, squares, and additions.
The schedule has **178 live operations: 117 multiplications, 29 additions,
32 subtractions**. A backward traversal checks every retained and new gate
is live. The previous unshared 184-operation attempt is preserved.
These costs are a substantial tradeoff: +81 operations and degree -2 relative
to 97/88. It is nondominated by the currently accepted listed 13-variable
frontier on variables/operations/degree, without any minimality claim.

For bounded symbolic work use the invertible linear coordinates
k=eta+zeta, zeta=k-eta, which preserve total degree even after specializing
all fixed ports. Write B=beta*J only in the following homogeneous formulas.
The full first norm has leader

    P22 = -B^14*k^2*s^4*w^2,

and direct expansion of the complete two norms gives

    deg S = 21,
    S21 = -4*B^13*k^2*s^4*w*(k-4*gamma).

The parent U88 degree-44 leader has a w-linear component

    -32*B^21*k^4*f^6*T^4*s^6*w*(K0*(B-F-alpha)-F)^2.

Multiplying by A makes this component divisible by S21. The explicit Hcorr
above has the required top two components. The remaining leading parts are
removed by the explicitly paid Bcorr; they are polynomial multiples of P22.
The probe retains seven layers below the propagated upper bounds, without
sharpening bounds at cancellations. The largest relevant bound is 49, so
all layers of degrees 42 through 49 are exact. It verifies that degrees
49 through 44 vanish, and records the entire nonzero degree-43 leader
(588 terms) of the stated Uc. These are sufficient to establish its degree;
unknown lower layers are not claimed to have been expanded or audited.

The lexicographically greatest unknown monomial in that leader is

    J^27*f^6*T*s^3*w^4*k^2,

with the single coefficient 64*beta^27. The complete actual-port check
verifies beta>0, so this coefficient remains nonzero at the current tuple.
The other two branches of (★) have degrees 80 and 72; subtracting A of
degree 1 does not change the auxiliary leader. The output therefore has
exact degree **86** and complete leading homogeneous polynomial Uc43^2.
Its lexicographically greatest monomial has coefficient 4096*beta^54.
This conclusion does not rely on a guessed generic coefficient surviving
specialization. The final square has not been fully expanded by this probe;
a complete per-gate graph/leader audit remains part of future materialization.

## Source and execution pins

Parent Lean sources, fully read for this proposal:

* `ThirteenUnitSphere96.lean`:
  `6589cdb6a7f4c97bd58eab10e6d3a05ff34189834f0660f8ca5eba3a3d954ab8`.
* `ThirteenCorrectedStrong.lean`:
  `57729066535acf1909d30ea5de0b4b78e1ac6f1ae11a126e1c2c4526cc546efe`.
* `ThirteenSecondFirstNormCorrections.lean`:
  `ea83a05732e96ebbadbab135f98018f5bcda115c887c1896b0f4be30a267bd22`.

The final exploratory paid script is SHA-256
`d88121f68a05a3434144d2bc9363e0efbd857313017490e27b6d481a74db808d`.
Its `PAID_LIFT_SHARED.json` is
`69ad8a3b4cca1d2acebd372aa88d76412201841ec41ba997e7a91e8d2cf87078`.
Normal and `python -O` runs both exited 0 and produced byte-identical JSON;
both logs are empty. Runtime was below one second per run under explicit
1GiB address-space, 30-second CPU, and 25,000-term caps. All source was read
before execution.

`PORTS.json`, SHA-256
`e94f516b2ef387dd8aa4c0af4b12209232b658bad7401160728acb7076c5dc35`,
pins each complete gzip and uncompressed port against the actual parent,
checks big-endian decoding/bit lengths, and checks the selected coefficients
are positive. Normal and optimized runs both passed with identical output
under 512MiB/10-second caps. It does not reprove the native tuple theorem.

`IMPORTED_SNAPSHOT.json`, SHA-256
`94f7d831adee512dfa97032d36079c963925942d758c3a8d5c648fba41e37008`,
pins the byte-identical exploratory snapshots imported from the old third
search directory. All subsequent work stays in this new namespace.
No prior committed search file, accepted graph, source, coefficient, display,
or shared build object was modified.

Before implementation: root review of this proposal; then a separately
owned Lean leaf/check pair and complete literal graph/auditor, with a newly
authenticated current parent overlay. No broader rebuild is proposed.
