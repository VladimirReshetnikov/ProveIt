# Thirteen positive unknowns, 77 operations, degree 96

This is a new zero-set presentation of the accepted normalized mixed-carrier
equation with 13 positive integer unknowns, 72 operations, and degree 124.
All thirteen unknowns and all four complete current2011 integer ports are
unchanged. The witness maps in both directions are the identity. The maintained
one-page equation is not changed by this packet.

The parent is `../thirteen-lv-carrier122/polynomial72.json`, SHA-256
`2ac2f00f08146d61b8d98c15b3f844b0ae00330eba825f80629d0a1e48e27045`.
Its ordinary proof is SHA-256
`0b4652adbdb5938ba52bf0865799acdc19dcbc13e23948ce16dc33c83cfd8386`.
The accepted entire-positive-zero arguments are implemented in
`ThirteenLVCarrier.lean`, SHA-256
`d64e31b377007ddd05964e29a1976c857d036d6eb919524df58c3bd8c237bd02`.

## Exact polynomial and domain

Use the parent coordinate order

`J,F,alpha,f,i,T,s,w,n,eta,zeta,m,gamma`.

Every coordinate is a strictly positive integer. The fixed port order is
`beta,K0,MC,MF`, with `MF` the source mask already shifted once by `beta`.
Write the following parent subexpressions (every operation is explicitly
scheduled in `polynomial.json`):

\[
\begin{gathered}
 b=\beta J,\quad q=b+1,\quad X=wq,\quad Y=sq^3,\quad E=XY,\\
 k=\eta+\zeta,\quad \ell=EkY,\quad c=kY+\eta,\quad a=E+Y,\\
 H=4a+3,\quad \Delta=a^2+H=(a+2)^2-1,\quad D=X+ac+\gamma H,\\
 C=q-F-\alpha,\quad
 R=((b(q-F)+\alpha)(q^2-1))+(M_C+qM_F)J,\\
 \tau=En+k-R,\quad P=\tau^2-\ell(\ell+k),\quad Q=D^2-\Delta c^2,\\
 G=(K_0+w)C-F,\quad L=cT-R,\quad V=f^2L-c,\\
 y=1+4\bigl(b(m-LVG)-G\bigr),\quad
 Z=f^2-\Delta(bic^2)^2,\\
 U=\Delta(f^2-1)(V^2-y^2)+y^2.
\end{gathered}
\]

The parent equation is `p72=PQUZ-1=0`. The new equation is

\[
 \boxed{p_{77}=(PQ-1)^2+(U-1)^2+(Z-1)^2=0.}
\]

The finite graph auditor checks the complete new tail as a formal polynomial
in four independent factors, not only numerical examples. It also preserves
every parent gate through `product0=P*Q` exactly.

## Entire positive zero-set equivalence

First suppose `p77=0`, over the integers. Every square is nonnegative, so each
vanishes. Thus `PQ=1`, `U=1`, and `Z=1`. Consequently `p72=0`. This implication
needs neither positivity nor an assumption about the signs of `P` and `Q`.

Conversely, suppose all thirteen coordinates are positive, `beta>0`, and
`p72=0`. The accepted parent entire-zero-set theorem supplies

\[
 Z=1,\qquad S^2V^2-(S^2-1)y^2=1,\qquad S=bi\Delta c^2.
\]

There is no premise here that the witness is canonical, that `y` is positive,
or that any individual norm already equals one. In Lean this is obtained by
`ThirteenLVCarrier.positive_zero_iff72` followed by `norms_of_zero`.
The first equality gives `f^2-1=Delta*(bic^2)^2`, whence

\[
 \Delta(f^2-1)=S^2.
\]

Substituting in the definition of `U`, the second equality gives `U=1`.
The original equation, together with `U=Z=1`, now gives `PQ=1`. Therefore
all three new residuals vanish and `p77=0`. No separate `P=Q=1` conclusion is
required by this proof. For arbitrary unconstrained factors, product one does
not suffice: `(-1)*(-1)*1=1` has nonzero square residuals. The norm theorem is
essential in this direction.

Both maps fix every coordinate, so they preserve positivity and are inverse
on the entire positive zero sets. Specializing the four ports to the actual
current2011 constants yields the external Lean theorem that absence of a
positive zero is equivalent to `DiophantineConsistency.ConZFC`, by composition
with the accepted parent endpoint. This is not an internal HA, PA, or ZFC
derivation and does not solve the pending arithmetized C222 calibration.

## Literal operation count and exact degree

The parent has 72 paid binary operations. Keep its first 69 rows, through
`product0=P*Q`; remove `product1`, `product4`, and the old output subtraction.
Append three residual subtractions, three squarings, and two additions.
This gives exactly 77 operations: 42 multiplications, 18 additions, and 17
subtractions. All 77 gates, all 13 coordinates, and all 4 ports are live.
Each square is a paid multiplication; integer literals are leaves.

For total degree in the thirteen unknowns, regard the four ports as fixed
coefficients and put `q0=beta*J`, `k0=eta+zeta`, and `C0=q0-F-alpha`.
The complete leading homogeneous forms of the factors are

\[
\begin{aligned}
 P_0&=-w^2s^4k_0^2q_0^{14} &&(22),\\
 Q_0&=8\gamma w^2s^3k_0q_0^{11} &&(18),\\
 U_0&=-16q_0^{22}k_0^4s^6w^4f^6T^4C_0^2 &&(48),\\
 Z_0&=-i^2w^2s^6k_0^4q_0^{22} &&(36).
\end{aligned}
\]

The norm `Q` has cancellation of its preliminary highest-degree terms;
the auditor expands its entire 323-term polynomial, checks an independent
algebraic expression, and uses the resulting full degree-18 leader. All
other gates have their full leading homogeneous forms propagated and
recorded, with any cancellation checked rather than assumed absent.

The three squared residual degrees are respectively 80, 96, and 72.
Therefore the sole degree-96 contribution is

\[
 U_0^2=256q_0^{44}k_0^8s^{12}w^8f^{12}T^8C_0^4.
\]

In particular the coefficient of
`J^48*eta^8*s^12*w^8*f^12*T^8` is exactly `256*beta^48`, which is strictly
positive for the actual current `beta`. This proves exact degree 96 after
specialization, not just a formal upper bound. The entire leader is recorded
in the finite certificate. The certificate also supplies exact modular
inequality witnesses of dependence on every unknown and every fixed port;
these are distinct from the zero-set proof.

## Scope of finite and Lean validation

The standalone standard-library auditor reads pinned source data, reconstructs
all four whole current2011 ports, compares every byte of their compressed
copies, checks the complete literal graph and algebraic tail, records all
gate leaders, and rejects corruptions of the residuals, squares, carrier,
ports, and graph schema. It imports no project program or incoming code.
Default and `python -O` invocations are read-only comparisons of deterministic
certificate bytes. Only `--write` materializes this new packet.

The separate Lean proof verifies the zero-set equivalence and actual-port
external consistency endpoint. Its initial leaf replay uses the accepted
frozen LV parent cache; it does not claim a newly refreshed source closure.
This is a degree/operation tradeoff, not a global minimality result: compared
with LV72 it adds five operations and reduces degree by 28, while preserving
13 unknowns and 47,313 raw coefficient bytes.
