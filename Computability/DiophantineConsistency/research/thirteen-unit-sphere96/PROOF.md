# Thirteen positive unknowns, 75 operations, degree 96

This equation has exactly the same entire positive integer zero set as the
accepted shared76/grouped77 equations, with identity witness maps. Its
polynomial is different: the new final equation is a three-square unit
sphere. All thirteen coordinates and four complete current2011 integer
coefficients remain fixed. The maintained equation.tex/PDF is unchanged.

The frozen76 graph is `../thirteen-shared-squares96/polynomial.json`, SHA-256
`3de1d43a810e694cb2f87fb15330e1decc6f5944c2302a18088cb8d3cfd15b36`.
Its ordinary proof is
`ed2d33cca9c948c5d9ce8c96997caee6b5e4b8305ae2616e19c9eab929c28fe3`,
and its Lean source is
`7f09a4e8448d643e09c5bfb2289f2d7640b1a0a5a2b2600fc53cce07d640eb97`.

## Complete equation

The strictly positive integer coordinates, in order, are
`J,F,alpha,f,i,T,s,w,n,eta,zeta,m,gamma`. The fixed ports are
`beta,K0,MC,MF`, with `MF` the source mask shifted by beta exactly once.
The beta port is positive; the uniform zero-set theorem imposes no further
condition on the other three ports. Define

\[
\begin{gathered}
b=\beta J,\quad q=b+1,\quad X=wq,\quad Y=sq^3,\quad E=XY,\\
k=\eta+\zeta,\quad\ell=EkY,\quad c=kY+\eta,\quad a=E+Y,\\
H=4a+3,\quad\Delta=a^2+H=(a+2)^2-1,\quad D=X+ac+\gamma H,\\
C=q-F-\alpha,\quad
R=(b(q-F)+\alpha)(q^2-1)+(M_C+qM_F)J,\\
\tau=En+k-R,\quad P=\tau^2-\ell(\ell+k),\quad Q=D^2-\Delta c^2,\\
G=(K_0+w)C-F,\quad L=cT-R,\quad V=f^2L-c,\\
y=1+4\bigl(b(m-LVG)-G\bigr),\quad h=f^2-1,\\
U=\Delta h(V^2-y^2)+y^2,\quad Z=f^2-\Delta(bic^2)^2.
\end{gathered}
\]

The equation is

\[
\boxed{p_{75}=(PQ)^2+U^2+Z^2-3=0.}
\]

## Entire positive zero set

First, for any integers A,B,C,

\[
A^2+B^2+C^2=3\quad\Longleftrightarrow\quad A^2=B^2=C^2=1.
\]

Each square on the left is at most three. An integer with square at most
three belongs to `{-1,0,1}`; thus each square is at most one. Their sum is
three only when each equals one. This complete integer argument requires
no nonzero assumption. It would be false over arbitrary commutative rings
or real numbers, and a sum of four squares equal to four has additional
solutions. Neither stronger statement is used.

The following negative-unit exclusions fix the signs for our actual
carrier. They are retained, already proved arithmetic lemmas, not finite
experimental evidence.

1. On every positive assignment, `x=E*Y≥2` and
   `P=tau²-x(x+1)k²`. The consecutive-factor negative Pell lemma gives
   `P≠−1`. Its elementary descending-coordinate proof is
   `ConsecutivePell.norm_ne_neg_one`, used in
   `ThirteenCorrectedStrong.first_ne_neg_one` with the actual parent
   coordinate restoration. No zero equation is assumed here.
2. For arbitrary integers a,u,v, `u²-((a+2)²-1)v²≠−1`, as follows
   modulo four. Apply `ShortEquation.strong_ne_neg_one` to `(a,D,c)`
   and `(a,f,bic²)` to obtain `Q≠−1` and `Z≠−1` without a positivity
   premise or previously decoded norm.
3. The two exclusions `P≠−1` and `Q≠−1` imply `PQ≠−1`. A product
   equal to −1 has integer unit factors; excluding −1 from each factor
   makes such a product impossible.

Suppose now `p75=0`. The integer sphere lemma gives
`(PQ)²=U²=Z²=1`. The exclusions above force `PQ=1` and `Z=1`.
The latter equality implies

\[
\Delta(f^2-1)=\Delta^2(bic^2)^2=(bi\Delta c^2)^2=S^2.
\]

Consequently `U=S²(V²-y²)+y²`. The square-coefficient auxiliary lemma
`ShortSystem.square_aux_ne_neg_one S V y` excludes `U=−1`, without
any size or sign requirement on S,V,y. This is used only after deriving
`Z=1`; there is no unconditional claim that the unspecialized U excludes
−1. Thus `U=1` and `PQ*U*Z-1=0`, the accepted72 product equation.

Conversely, for every positive zero of that accepted72 equation,
`ThirteenGroupedSquares96.residuals_of_positive72_zero` gives the exact
three equalities `PQ=U=Z=1`, hence `p75=0`. Both directions retain all
thirteen coordinates identically, and therefore preserve every positive
zero, rather than merely exhibiting a canonical family.

The parent76 polynomial is `(PQ-1)²+(U-1)²+(Z-1)²`. It is not identical
to p75. For example, at independent factor values `(PQ,U,Z)=(2,1,1)`,
the parent value is one and the new value is three. Finite formal tests
bind the new graph to the displayed sphere formula; the actual zero-set
equivalence is established by the sign argument and Lean proof above.

## Literal schedule and exact degree

Retain the shared `h=f²-1` and auxiliary computation. Replace the old
strong residual row `resZ=h-strong_term` with `Z=f²-strong_term`.
Delete the two rows `resPQ=PQ-1` and `resU=U-1`; square PQ,U,Z directly.
Retain the two sum rows and append subtraction of three. This makes
75 paid binary operations:42 multiplications,18 additions,15 subtractions.
The other69 parent rows are unchanged in relative order. Every row,
coordinate and whole port remains live; squares cost multiplications and
all scalar constants are integer leaves.

The changes to raw factors affect only lower degrees, so their respective
degrees are22,18,48,36 for P,Q,U,Z, and80,96,72 for the three squares.
The finite auditor nevertheless recomputes every gate's full leading
homogeneous form, including the entire323-term main-norm cancellation.
Writing `q0=beta*J`, `k0=eta+zeta`, `C0=q0-F-alpha`, the full degree96
leader is

\[
256q_0^{44}k_0^8s^{12}w^8f^{12}T^8C_0^4.
\]

It has135 terms; the coefficient of
`J^48*eta^8*s^12*w^8*f^12*T^8` is exactly256*beta^48, positive at the
actual ports. All four whole coefficients are reconstructed from the
pinned3297-entry native array. They are unchanged:47,313 raw bytes and
4,230 gzip bytes, with MF shifted exactly once.

## Proof and validation boundary

`ThirteenUnitSphere96.lean` proves the integer sphere lemma, every needed
negative-unit exclusion, both identity positive-zero maps, exact evaluation
of the new multivariate polynomial and the actual external
`DiophantineConsistency.ConZFC` no-positive-zero endpoint. No internal HA,
PA or ZFC derivation, consistency assertion or global minimum is claimed.

The standalone finite auditor separately proves graph-to-formula equality,
all75 operation and liveness checks, every degree/leader and whole-port
identity. It executes only newly authored standard-library code and treats
all pinned project/incoming artifacts as data. Normal and optimized runs
compare deterministic output bytes; only `--write` materializes this new
packet. The finite metric calculation is not a Lean totalDegree theorem.
