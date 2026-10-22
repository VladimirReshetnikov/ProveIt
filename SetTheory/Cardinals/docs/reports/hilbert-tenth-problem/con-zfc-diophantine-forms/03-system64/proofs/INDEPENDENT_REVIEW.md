# Independent mathematical review of fixed-marker Diophantine systems

**Result: PASS, conditional on the explicitly identified upstream compiler
and Pell theorems.** The seven-equation ordinary system has sixteen strictly
positive integer unknowns, maximum equation degree 28, and a complete
64-operation comparison source. The six-equation eliminated-root system has
fifteen strictly positive integer unknowns and maximum equation degree 244.
Its single-polynomial version has degree 295 and an 82-operation source.

This review supplies a mathematical proof and an independent executable
source audit. It is **not a Lean or Rocq kernel check**. The review does not
claim to have re-proved the historical universal compiler. It also does not
turn an arbitrary tuple of fixed numerals into a valid compiler instance.
Instantiating the fixed-program numerals for the chosen contradiction-search
machine remains a separate, essential part of the overall construction.

## 1. Exactly what is being reviewed

The author data are `fixed_marker_variants.json` and
`fixed_marker_systems.json`. They are derived from these actual upstream
packets in `Papers/research-wip/native-stream-queue`:

* `complete84_scaled_strong_output.json`;
* `complete85_reduced_auxiliary_degree.json`;
* `complete86_ordinary_auxiliary_projection.json`;
* `complete92_norm_unit_guard.json`.

The independent helper `review_fixed_marker.py` reads all of these as inert
JSON. It neither imports nor executes the author's generator or any
historical Python. The companion receipt `fixed_marker_review.json` records
the exact SHA-256 pins, all source counts, full row reconstruction, direct
comparison interfaces, and independent degree diagnostics.

The fixed-program hypotheses are the **entire inherited complete75 compiler
recipe**. In particular, write

\[
B=2^d\ge16,\qquad b>0\text{ odd},\qquad
u=2d+b,\qquad W_0=2^bB^2=2^u.
\]

The coefficient ports have their actual meanings
`Bm1=B-1`, `twice_cell_bits=2d`,
`Kconstant=DC+B*DR`, and
`MF=MF_native+B-1`. Their full mask, synchronization, and machine-layout
conditions are retained. The new `marker_constant` is the fixed integer
\(W_0\); it is not an extra existential variable. The ordinary input has
been fixed to \(x=1\).

All supplied witnesses below are strictly positive integers. The sixteen
coordinates are

\[
J,F,\alpha,t,f,h,i,T,s,w,\tau,\eta,\zeta,y,Z,\gamma.
\]

Here \(t\) is the transport quotient and \(T\) the auxiliary quotient.
The fifteen-coordinate version deletes \(f\). Computed abbreviations are
polynomials and do not add existential coordinates:

\[
\begin{gathered}
q=(B-1)J+1,\quad X=wq,\quad Y=sq^3,\quad E=XY,\\
k=\eta+\zeta,\quad c=kY+\eta,\quad a=Y(X+1),\\
A_0=a+2,\quad \Delta=A_0^2-1,\quad H=4a+3,\\
D=X+ac+\gamma H,\quad C=q-F-Z-\alpha-2d,\quad W=C-Z,\\
R=(q^2-Z-qF)(q^2-1)+(MC+qMF)J,\\
N_k=k-hE-R,\qquad
N_t=(Kconstant+w)C+q-F-t(q-1),\\
V=c(Tf-1)-Rf^2.
\end{gathered}
\]

The first and main norm factors referred to below are explicitly

\[
N_{first}=\tau^2-XY^2(XY^2+1)k^2,\qquad
N_{main}=D^2-\Delta c^2.
\]

The source evaluates the first subtracted term as \(L(L+k)\), where
\(L=E(kY)=XY^2k\); this is the same polynomial.

The distinction between \(A_0\) and the source register `A` is essential:
the register `A` represents \(\Delta\), not \(A_0\).

## 2. The fixed-marker transformation

The old main root used \(\rho+\sigma\). Replace this sum by one free positive
witness \(\gamma\), delete \(\delta,\rho,\sigma\), and replace the input norm
factor by

\[
M=1+(W-W_0)^2.
\]

For product polynomials, \(M\) is a positive integer. If the full product is
one, every factor is an integer unit, so \(M=1\), hence \(W=W_0\).
For a comparison system, impose \(W=W_0\) directly and omit all three gates
that compute \(M\).

For the scaled normalized polynomials, first cancel the known positive
factor \(\Delta\), exactly as in the upstream complete84 proof. One must
not infer that the seven scaled factors are individually units from their
product being \(\Delta\).

The main new point is that the old input witnesses can be restored using
only the recovered main Pell rank. No new power-recovery, population-count,
or machine-decoding argument is needed in this transformation.

## 3. Input-independent rank lemma and its audit boundary

Write \(\chi_A(j),\psi_A(j)\) for the Pell sequences defined by

\[
(A+\sqrt{A^2-1})^j
 =\chi_A(j)+\psi_A(j)\sqrt{A^2-1}.
\]

### 3.1 Normalized strong source

The normalized local factors are

\[
N_s=f^2-\Delta i^2c^4,\quad
Q=\Delta^2i^2c^4,\quad
N_a=QV^2-(Q-1)y^2.
\]

Together with the first and main norm equations, the index and transport
unit conditions, and the positive supplied coordinates, the upstream
normalized rank proof gives

\[
R\text{ odd},\quad
D=\chi_{A_0}(R),\quad c=\psi_{A_0}(R),\quad
N_k=N_t=1.
\tag{R}
\]

This conclusion remains valid when \(T\) is any integer, provided \(f>0\).
The required signed version is the argument in
`complete84_signed_quotient_absorption.md`, Section 2. The ordinary positive
version is in `review_complete85_auxiliary_bezout_math.md`, Sections 2--6.

The following dependency audit is decisive:

| Upstream argument | Use of the old input block | Why the marker version satisfies it |
|---|---|---|
| Unit-sign exclusions | The input norm is an integer unit and cannot be -1 | The marker factor is positive, so its unit value is +1 |
| Transport and packing bounds | No input Pell equation; uses the positive transport quotient and raw slack | These rows and positive coordinates are unchanged |
| Main-root classification | Uses positivity of \(D=X+ac+(\rho+\sigma)H\) | \(D=X+ac+\gamma H>0\) follows from \(\gamma>0\) |
| First-rank congruence and ratio interval | No \(\delta,\rho,\sigma\) | The rows for \(k,c,E,R\) are unchanged |
| Normalized auxiliary rank | No input root or input exponent | The local strong equation is unchanged |
| Signed auxiliary step-down | Uses absolute auxiliary root and two congruences | These remain true for every signed \(T\) |
| Final index-sign exclusion | Uses only \(kY<c<k(Y+1)\), Pell duplication, and the recovered rank | All are unchanged |

In particular, none of these arguments requires \(\gamma\ge2\) before
the equations hold. Positivity suffices. The stronger conclusion
\(\gamma\ge2\) will follow from restoration of \(\rho,\sigma>0\).

For clarity, the raw bounds used before typing are

\[
q\ge B\ge16,\quad R>3q+1,\quad R+2<q^4\le E<a.
\tag{B}
\]

The first norm is
\(\tau^2-U(U+1)k^2=1\), \(U=XY^2>1\). Its fundamental positive unit
has second coefficient 2, giving \(k=2\psi_{2U+1}(n)\).
The index unit yields \(2n\equiv R+\epsilon\pmod E\),
\(\epsilon\in\{-1,1\}\). The main norm gives a rank \(p>n\ge24\).
The normalized strong equation gives a rank \(m\) with
\(pc\mid m\), and the two auxiliary congruences give
\(R\equiv\pm p\pmod c\). Since \(0<R,p<c/2\), one gets \(p=R\).
The ratio interval excludes \(\epsilon=-1\), giving (R).
These are precisely the imported rank steps; the review does not replace
them by finite numerical examples.

### 3.2 Ordinary strong source

For the recommended low-degree comparison system the strong equation is

\[
(ic^2)^2=\Delta(f^2-1),\qquad Q=\Delta(f^2-1),
\qquad N_a=QV^2-(Q-1)y^2=1.
\tag{O}
\]

The appropriate imported proof is
`complete86_ordinary_auxiliary_projection.md`, Sections 3--5, together with
`review_complete86_ordinary_auxiliary_math.md`, Sections 2--4, and the
generic middle lemma of `PELL_RELAXED_AUXILIARY_PROOF.md`.
These texts were read in full for this review.

The first/main equations and raw bounds first give
\(c=\psi_{A_0}(p)>A_0\Delta^2\). The relaxed-rank lemma then gives

\[
f=\chi_{A_0}(m),\qquad ic^2=\Delta\psi_{A_0}(m),
\qquad p\mid m,\qquad c\mid m.
\]

Strong divisibility gives \(c^2\mid f^2-1\). The size margin implies
\(f>2c\) and \(Q-Rf^2-c>0\). With \(T>0\), the auxiliary root-gap
argument forces \(V>0\); the same two congruences give \(p=R\), and the
same ratio argument fixes the index sign. Thus (R) also holds here.

It would be incorrect to import the stronger normalized assertion
\(c^2\mid\psi_{A_0}(m)\) into this ordinary proof. Only the displayed
ordinary divisibilities are needed. The ordinary proof is independent of
the deleted input block in the same way as the normalized proof.

At the seven separate comparison equalities, all norm values and
\(N_k=N_t=1\) are imposed directly, so no unit-sign argument is needed.

## 4. Full restoration of the three deleted witnesses

Assume the marker equation and (R). Since \(W=C-Z=W_0\),

\[
q=F+2Z+\alpha+2d+W_0>W_0=2^u>u.
\]

Together with (B), this gives \(u<R\). Both \(u\) and \(R\) are odd,
so \(R\ge u+2\). In particular \(u\ge3\).

Define

\[
\kappa=\psi_{A_0}(u),\qquad \mu=\chi_{A_0}(u),
\]

and put

\[
\delta=\frac{\kappa-u}{\Delta},\qquad
\rho=\frac{\mu-a\kappa-W_0}{H},\qquad
\sigma=\gamma-\rho.
\tag{I}
\]

The following proves that these are strictly positive integers. None of
them is computed by division in the emitted circuit; they are witnesses
whose existence is established in the correctness proof.

### 4.1 Integrality and positivity of delta

Pell expansion modulo \(\Delta=A_0^2-1\) gives

\[
\psi_{A_0}(j)\equiv jA_0^{j-1}\pmod\Delta.
\]

For odd \(u\), \(A_0^{u-1}\equiv1\pmod\Delta\), so
\(\Delta\mid\kappa-u\). The recurrence gives
\(\psi_{A_0}(j)>j\) for \(j\ge2\), \(A_0\ge2\).
Thus \(\delta\) in (I) is a positive integer.
Also \(\kappa<c\), by strict growth and \(u<R\); hence the historical
input-gap witness \(c-\kappa\), if required at an earlier interface,
is positive.

### 4.2 Integrality and positivity of rho

Define the projection sequence

\[
E_A(j)=\chi_{A_0}(j)-a\psi_{A_0}(j)
       =2\psi_{A_0}(j)-\psi_{A_0}(j-1),\quad j\ge1.
\]

It has \(E_A(0)=1\), \(E_A(1)=2\), and recurrence
\(E_A(j+2)=2A_0E_A(j+1)-E_A(j)\).
Since \(4-4A_0+1=-H\), the sequence \(2^j\) obeys the same recurrence
modulo \(H\). Therefore

\[
E_A(j)\equiv2^j\pmod H.
\]

Because \(W_0=2^u\), the numerator defining \(\rho\) is divisible by
\(H\). Furthermore \(E_A(2)=4A_0-1>4\), and its positive increasing
recurrence gives \(E_A(j+1)>2E_A(j)\) for \(j\ge1\).
Consequently \(E_A(u)>2^u\) for \(u\ge2\), proving \(\rho>0\).

### 4.3 Positivity of sigma

The main-root equation and (R) give
\(E_A(R)=X+\gamma H\). The definition of \(\rho\) gives
\(E_A(u)=W_0+\rho H\), hence

\[
H(\gamma-\rho)=E_A(R)-E_A(u)-X+W_0.
\tag{G}
\]

For every positive \(j\),
\(\psi_{A_0}(j)<E_A(j)\le2\psi_{A_0}(j)\).
Writing \(y_j=\psi_{A_0}(j)\), the recurrence and \(y_{u-1}<y_u\) give

\[
y_{u+2}-2y_u
 >(4A_0^2-2A_0-3)y_u>A_0.
\]

Since \(R\ge u+2\), it follows that

\[
E_A(R)-E_A(u)>y_{u+2}-2y_u>A_0>X.
\]

The last inequality follows from \(a=Y(X+1)>X\).
Equation (G) therefore proves \(\sigma=\gamma-\rho>0\).
This is the gamma-dominance argument in
`complete75_gamma_dominance_elimination102.md`, Section 3, with all
hypotheses now independently supplied.

### 4.4 Exact restoration of the original input equations

By construction,

\[
\kappa=u+\delta\Delta,\quad
\mu=W_0+a\kappa+\rho H,\quad
\mu^2-\Delta\kappa^2=1,\quad
\gamma=\rho+\sigma.
\]

Thus the original input factor is exactly 1, the main root is unchanged,
and every other retained source row has its original value. The restored
tuple is a zero of the literal upstream polynomial at \(x=1\).
This is a zero-set restoration argument, not an identity on all off-zero
positive tuples.

Conversely, the original positive input theorem at \(x=1\) gives
\(W=W_0\). Delete \(\delta,\rho,\sigma\), set
\(\gamma=\rho+\sigma\), and the fixed-marker equations hold. Therefore
the accepted input proposition is unchanged. At a zero the old input rank
is uniquely \(u\), so (I) is also the inverse on the deleted coordinates.

**Crucial simplification:** the proof in this section never assumes
\(X=2^R\), a typed radix, a binomial identity, or a decoded computation.
It restores the original interface immediately after main-rank recovery.

## 5. Eliminating the strong root: fifteen variables

This section applies to the normalized fixed-marker source. Retain
\(T,i,y>0\) and delete \(f\). Define

\[
\begin{gathered}
S=\Delta ic^2,\quad Q=S^2,\quad
D_*=1+\Delta i^2c^4,\quad b_*=c+RD_*,\quad v_*=cT,\\
A_*=Q(D_*v_*^2+b_*^2)-(Q-1)y^2-1,\qquad
B_*=2Qv_*b_*,\\
K_*=A_*^2-D_*B_*^2,\qquad
P=N_{first}N_{main}M N_kN_t.
\end{gathered}
\]

The new polynomial is

\[
P(K_*+1)-1=0.
\tag{F}
\]

These are precisely the upstream complete92 local-norm formulas with the
new marker and free \(\gamma\). Its algebraic proof does not use an input
Pell equation.

### 5.1 The denominator never vanishes

Before imposing any equation, \(D_*>c>0\). If \(R\ge0\) then
\(b_*>0\); if \(R\le-1\), then \(b_*\le c-D_*<0\).
Thus \(b_*\ne0\) and \(B_*=2QcTb_*\ne0\).
No sign of \(R\), computation, or index equation is assumed here.

### 5.2 Integral root reconstruction

At a zero of (F), \(P\) and \(K_*+1\) are integer units. Since
\(B_*\) is even,

\[
K_*+1\equiv A_*^2+1\pmod4,
\]

which is 1 or 2 modulo 4 and cannot be -1. Hence \(K_*=0\), \(P=1\).
Define the rational number \(f=A_*/B_*\). It satisfies \(f^2=D_*\),
so it is an integer: in lowest terms, a denominator dividing its squared
integer numerator must be 1. It is nonzero because \(D_*>0\).

Substitution gives the normalized strong factor 1 and auxiliary norm 1;
therefore this signed \(f\) restores a zero of the sixteen-variable
normalized marker polynomial. The rational formula also proves uniqueness.
The identities used are the exact all-ring identities in
`complete92_norm_unit_guard.md`, Sections 2--4; their factor interfaces are
preserved by the audited literal source transformation.

### 5.3 Why the reconstructed integer f is positive

Suppose \(f<0\). Simultaneously replace \((f,T)\) by \((-f,-T)\).
Every retained expression is unchanged: the only direct occurrences of
\(f,T\) are \(f^2\) and \(Tf\). We obtain a marker zero with \(f>0\)
and \(T<0\), with every other supplied coordinate positive.

Apply the input-independent signed rank lemma of Section 3.1. Its proof
allows any signed \(T\). Section 4 then restores positive
\(\delta,\rho,\sigma\), producing a zero of the **original complete84
source**, with \(f>0\), all other coordinates positive, and only \(T\)
allowed signed.

Now apply the established source-specific theorem in
`complete84_signed_quotient_soundness_scout.md`, as independently reviewed
in `review_complete84_signed_quotient_soundness.md`: on a valid compiler
slice, every such original zero has \(T>0\). This contradicts \(T<0\).
Therefore the reconstructed \(f\) is positive.

This ordering avoids applying a positive-domain theorem prematurely. It
also avoids re-proving the historical power/population/parity argument for
the modified circuit: the original signed theorem is used only after the
original input interface has been restored.

Conversely, any positive sixteen-variable normalized marker zero has
\(f^2=D_*\), \(A_*=B_*f\), and all normalized factors 1. Deleting \(f\)
therefore gives (F). This proves exact projection equivalence.

The six-equation comparison variant requires
\(N_{first}=N_{main}=N_k=N_t=1\), \(W=W_0\), and
\(A_*^2=D_*B_*^2\). These imply (F) immediately. Conversely, the previous
reconstruction and rank proof restore the individual factors to 1, so
the comparison system and polynomial are equivalent on the stated domain.

## 6. Recommended ordinary seven-equation system

Use the ordinary definitions (O), and impose

\[
N_{first}=1,\quad N_{main}=1,\quad N_k=1,\quad N_t=1,
\quad N_a=1,\quad (ic^2)^2=\Delta(f^2-1),\quad W=W_0.
\]

The literal `fixed_marker76_system` source computes these seven comparison
pairs in 64 operations: 34 multiplications and 30 additions/subtractions.
The strong comparison uses the existing `ic22` and `R16` values directly,
omitting the two unnecessary rows that subtract them and then add 1.
The marker equality also omits its square-plus-one wrapper, and the system
has no product finalizer.

There are exactly sixteen supplied positive witnesses. The residual degrees
are, in the displayed source order,

\[
22,18,7,2,28,22,1.
\]

The maximum is 28. This degree concerns the polynomials after expanding
all computed abbreviations, not merely the degrees of individual gates.
The sum of the seven squared residuals is a single nonnegative polynomial
of exact degree 56. Its complete emitted evaluator has 84 operations,
including all residuals, squares, and sums.

## 7. Uniform degree argument

Give each witness degree 1 and every genuine fixed numeral degree 0.
Let

\[
Q_0=(B-1)J,\quad k_0=\eta+\zeta,\quad
L=Q_0-F-Z-\alpha,\quad L_W=Q_0-F-2Z-\alpha,\quad
L_t=wL-tQ_0.
\]

The first and main factors have respective leading forms

\[
-w^2k_0^2s^4Q_0^{14},\qquad
8\gamma w^2k_0s^3Q_0^{11},
\]

of degrees 22 and 18. For the main factor, the cancellation is checked
before degree counting using the exact identity

\[
(X+ac+g)^2-(a^2+H)c^2
 =X^2+2Xg+g^2+2acX+2acg-Hc^2,
\qquad g=\gamma H.
\]

The index and transport leading forms are
\(-hwsQ_0^4\) and \(L_t\), of degrees 7 and 2.
The marker leading form is \(L_W^2\), of degree 2.
For the ordinary auxiliary factor the leading form is

\[
w^2k_0^2s^4Q_0^{14}T^2f^4,
\]

of degree 28, while the ordinary strong residual has leading form
\(i^2k_0^4s^4Q_0^{12}\), of degree 22.

Every displayed form is a nonzero polynomial for every \(B>1\): in
particular \(L_t\) has the unique term \(-(B-1)tJ\), and \(L_W\)
has coefficient -1 at \(\alpha\). The coefficient ring is an integral
domain. Thus multiplying the factor leaders proves uniform exact degrees
157, 125, and 101 for the 74-, 75-, and 76-operation marker polynomials.
These are the upstream factor-degree sums with the degree-32 input norm
replaced by the degree-2 marker; no zero-only identities are used.

For the fifteen-variable polynomial, \(P\) has exact degree 51.
The local norm ingredients have degrees

\[
\deg Q=46,\quad \deg D_*=34,\quad \deg R=4,
\quad \deg b_*=38,\quad \deg A_*=122,
\quad \deg(D_*B_*^2)=214.
\]

The degree-244 term of \(A_*^2\) therefore survives, and (F) has exact
degree \(51+244=295\). Its comparison system has maximum residual degree
244. For the ordinary sum of squares, only the auxiliary residual has
degree 28, so its squared leading form cannot cancel:

\[
w^4k_0^4s^8Q_0^{28}T^4f^8.
\]

This proves exact degree 56 uniformly. The independent finite coefficient
executions corroborate these calculations; they do not replace the
uniform argument.

## 8. Independent executable evidence and remaining boundaries

The reviewer helper passed on all four full polynomials, three comparison
systems, and the ordinary sum of squares. It independently:

1. authenticates all four upstream JSON files against the author's pins;
2. reconstructs every transformed row and checks all free-coordinate maps;
3. checks acyclic ordering, exact liveness, and multiplication/addition counts;
4. traverses the full output cone at the factor interface and verifies every
   factor is used exactly once with the correct final target;
5. reconstructs each comparison source as the exact live subarray of its
   reviewed polynomial;
6. checks the two removed ordinary-strong rows and the direct local-norm
   comparison against their literal definitions;
7. checks 32 rational assignments against the full ordinary residual sum;
8. executes independent full univariate coefficient calculations at two
   diagnostic assignments for every delivered circuit or system.

The scripts use explicit exceptions and remain active under `python -O`.
The receipt labels these results as source/algebra checks, not proof of
the historical machine compiler and not kernel verification.

The logical dependency for the final application is:

* a valid fixed-program export recognizes the intended contradiction search;
* the upstream compiler theorem represents that program's acceptance;
* this review proves the fixed-marker and root-elimination transformations;
* the separate K215 or proof-enumerator correctness theorem identifies
  acceptance with inconsistency of ZFC.

No global minimum in variable count, degree, number of equations, coefficient
height, or arithmetic operations is claimed. Fixed numerals are charged as
constants in the stated source model; their description lengths must still
be documented in the actual ZFC instantiation.
