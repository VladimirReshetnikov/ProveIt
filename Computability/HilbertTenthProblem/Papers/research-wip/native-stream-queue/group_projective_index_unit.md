# The native index unit saves one more polynomial addition

The complete [merged first-root compiler](group_projective_first_norm_unit.md)
can absorb its first-index comparison into the existing unit product.
This adds **one multiplication and one subtraction** to the certificate,
removes one comparison, and saves **one addition** in the single
sum-of-squares polynomial. The supplied positive coordinates and their
positive zero set are unchanged.

The additional factor has no unconditional negative-unit exclusion.
Its negative branch is ruled out using the retained strong auxiliary
equation, the bound X>r and **both** positive ratio slacks. The proof
starts with only a signed checksum. It restores the checksum and index
equations before invoking Boolean typing, range or history decoding.
No ordinary-input condition or fixed compiler numeral changes.

Write the padded-program certificate cost, before the two local norm
successors, as

    C0=3m+3h+p+185+f_flow−3min(h,3)−epsilon.

Keep all its fixed-table hypotheses, including the fixed-numeral margin
`alpha+beta+1≥m`. Here epsilon=1 is controller-mask reuse (m≥8), and
chi=1 denotes computed P. The complete new ledgers are

| Computed native fields | Certificate | Equations | Positive witnesses | SOS polynomial |
|---|---:|---:|---:|---:|
|a,d,k,s|C0+3|16−chi|m+34−chi|C0+50−3chi|
|a,c,d,k,r,s|C0+3|14−chi|m+32−chi|C0+44−3chi|

These are fixed-table compiler formulas, not numerical bounds for an
instantiated universal matrix alphabet. The separate 75/88 frontiers are
unchanged. The [source](group_projective_index_unit.py) exports a local
`rewrite(old_packet)` for composition, and the
[receipt](group_projective_index_unit.json) audits the exact source and
degree claims below.

## 1. Equations and signs available at a new zero

Use the native quantities

    X=wq, Y=sq, E=XY, k=eta+zeta, c=kY+eta,
    a=Y(X+1), A=a+2, Delta=A²−1, H=4a+3,
    Jtarget=2r+1, U=jc−Jtarget,
    T=ic², Pfirst=2XY²+1.

All displayed defining comparisons or their computed aliases remain.
In particular, eta,zeta>0 give the full interval

    kY<c<k(Y+1).                                    (1)

The three norm factors are exactly the parent's

    N0=g²+4XY²k(g−k),
    N1=d²−Delta*c²,
    N3=T²(U²−y²)+y².

Each excludes −1 modulo 4 on every integer assignment. The old unit
product is `N0*N1*N3*Q=1`, where `Q=q−sum_i Fi`. Replace it and
the first-index equation `k=r+1+hE` by

    N0*N1*N3*Q*Nk=1, Nk=k−r−hE.                    (2)

At a zero, all five factors are integer units. The three norm signs
therefore give

    N0=N1=N3=1, Q=Nk=epsilon_k in {−1,1}.           (3)

The symbol epsilon_k is unrelated to the controller-mask option
epsilon in the cost table. No checksum typing or index equality has
been assumed in (3).

The strong comparison and auxiliary linear comparison remain exactly

    T²=Delta(f²−1), U=of−c.                        (4)

We do not substitute (4) into an off-zero polynomial or remove either
comparison. The positive first-root inverse from the parent gives
`root=2XY²k+g=2tau+1`, with tau>0 an integer, and hence the original
triangular first norm. This inverse uses only N0=1 and positive X,Y,k,g.

## 2. Strict bounds with the checksum still signed

Before any equations, the positive group source computes P≥1 and
`q=16P^L≥16`; computed P uses the nonnegative sum `sum(Ehat_e−1)`.
The three supplied selector fields are positive, and the fourth
computed field is positive by its explicit padded definition
`F3=16Z_joined+8`, with Z_joined≥0. These facts require no Boolean
typing. The retained packing and bound give

    r=F0+qF1+q²F2+q³F3, X=r+bound_beta>r.

Equation (3) says only `sum_i Fi=q−epsilon_k`, so the sum is q−1 or
q+1. Positivity alone implies

    q³+q²+q+1≤r≤(q−2)q³+q²+q+1<q⁴,
    r≥4369.                                        (5)

For the upper estimate, allow the larger sum q+1, assign one unit to
each of the three lower fields, and put all remaining mass in F3.
No no-carry or individual bit condition is used.

The retained odd-scale definition gives s>0, and therefore Y≥q≥16.
Consequently

    E=XY>2r+1, a=Y(X+1)>2r+1, Pfirst>A.            (6)

The first norm classifies k as

    k=psi_Pfirst(n), n≥1.

This is the same elementary triangular Pell classification used in the
[native selector proof, Sections 1–2](native_controller_binary_selector56.md).
Since Pfirst≡1 modE, its recurrence gives `k≡n modE`. The new index
unit thus yields

    n≡r+epsilon_k modE, n≥r−1.                    (7)

Indeed both r−1 and r+1 lie strictly between0 and E. The positive main
root and N1=1 give `c=psi_A(p), d=chi_A(p)` for p≥1. Since
Pfirst>A and c>k, monotonicity of the psi sequence forces p>n. Thus

    p≥r≥4369,
    c>A*Delta², c>2p,
    c>Yk≥Y(r−1)>2(2r+1).                           (8)

The large-index bound follows, for example, from
`c>(2A−1)^(p−1)>A^6>A*Delta²`; ordinary Pell growth gives c>2p.
The last inequality uses only Y≥16 and r≥4369. In particular both
p and Jtarget are strictly less than c/2. None of (5)–(8) uses Q=1,
a power-of-two conclusion, a decoded field, or an exact Pell index.

## 3. Recovering the main index from the unchanged strong equations

Apply the integral-rank and divisibility arguments in
[the relaxed auxiliary proof](../../1980/PELL_RELAXED_AUXILIARY_PROOF.md)
to (4). Their needed hypotheses here are exactly

    A>1, c=psi_A(p)>A*Delta²,
    T=ic²>0, T²=Delta(f²−1), i>0.

They give a positive auxiliary index ell_aux with

    f=chi_A(ell_aux), c divides ell_aux,
    T=Delta*psi_A(ell_aux), ell_aux≥c>2p.            (9)

The original proof's historical choice of A=a+4 is not needed by those
rank/divisibility arguments; they concern any A>1 and Delta=A²−1.
Here A=a+2 throughout. The independent bounds (8) provide precisely
the size input that its proof uses.

Also U=jc−Jtarget>0, since j≥1 and c>2Jtarget. The auxiliary norm is

    (TU)²−(T²−1)y²=1.

As T=ic²>1 and y>0, Pell classification gives an odd index
`ell=2v+1` and `TU=chi_T(ell)`, `y=psi_T(ell)`. An even index is
impossible because `chi_T(2v)≡(−1)^v modT`, while T divides TU.
The integer odd-index polynomials from
[the half-parameter proof, Sections 3–4](../../1980/HALF_PARAMETER_PELL_92_PROOF.md)
give

    U≡(−1)^v psi_A(ell) modf,
    U≡(−1)^v ell modc.                              (10)

The first follows from `T²≡−Delta=1−A² modf`; the second from
T≡0 modc. Meanwhile the unchanged linear comparisons give
`U≡−c modf` and `U≡−Jtarget modc`.

Squaring the first congruence in (10), using c=psi_A(p), and applying
the chi doubling identity yields

    chi_A(2ell)≡chi_A(2p) mod chi_A(ell_aux).

The retained signed chi step-down lemma applies because
`0<2p<ell_aux`. It gives `ell≡±p mod ell_aux`, hence modulo c by
(9). Combining with the second congruence in (10) gives

    Jtarget≡±p modc.

The strict bounds `0<Jtarget,p<c/2` exclude the negative alternative
and every nonzero multiple of c. Therefore

    p=Jtarget=2r+1.                                (11)

This is the generic rank and signed-index argument, not an invocation
of the whole native theorem with its checksum assumed in advance.
No parity of r or any decoded stream has been used.

## 4. The upper ratio excludes the negative index unit

Because n<p=2r+1<E, (7) now identifies the exact representative

    n=r+epsilon_k.                                 (12)

If epsilon_k=−1, then p=2n+3. Put `Q2=chi_A(2)=2A²−1`.
Direct substitution of A=Y(X+1)+2 shows Q2>Pfirst, and 2A>Y+1.
Pell duplication and monotonicity give the exact inequality

    psi_A(2n)=2A*psi_Q2(n)
               ≥2A*psi_Pfirst(n)=2Ak>k(Y+1).

Since p=2n+3, c=psi_A(p)>psi_A(2n), contradicting (1). Thus

    Nk=Q=1.                                       (13)

The old index equation and checksum are restored. Along with the three
norms, (4) and every unchanged comparison, this is the full parent
positive tuple. The parent's typing, selected-source, geometry, range,
controller and ordinary-input theorems can now be applied in their
original order. Conversely every parent positive zero has Nk=1 and
therefore satisfies (2). The two sources have exactly the same positive
witness vectors; no coordinate map beyond the already inherited
first-root map is introduced by this successor.

## 5. Two new gates and the exact residual identity

The parent pays `r1=r+1` and `R11=r1+hE`. The former is also needed
for the main target `2r+1`, so it remains. Change just

    R11=k−hE

at the same one-subtraction cost, and add

    index_unit=R11−r,
    five_units=four_units*index_unit.

The source obtains the correct r register from the existing r1 gate:
it is supplied in the four-field variant and the existing packed alias
in the six-field variant. This is register reuse, not an omitted
operation. Delete the old comparison k=R11 and replace four_units=1
by five_units=1. No other parent register depends on R11.

If r_index and r_four are the old residuals with source orientations
`k−(r+1+hE)` and `four_units−1`, then, on arbitrary integer assignments,

    index_unit=r_index+1,
    r_new=(r_four+1)(r_index+1)−1.                  (14)

Every other residual is identical. The new SOS deletes the two old
squares and adds r_new². This exact identity is audited without using
the conditional sign proof to simplify off-zero expressions.

Relative to the merged first-root parent, the certificate adds 1M+1A
and loses one equation. Its SOS loses one residual square and two
additions, so the net saving is exactly 1A. Writing the inherited common
register savings as d_M,d_A, the new certificate split is

    M=m+2h+84+f_M−d_M−epsilon,
    A=2m+h+p+104+f_A−d_A.

The SOS splits are

    four: M=m+2h+100+f_M−d_M−epsilon−chi,
          A=2m+h+p+135+f_A−d_A−2chi;
    six:  M=m+2h+98+f_M−d_M−epsilon−chi,
          A=2m+h+p+131+f_A−d_A−2chi.

## 6. Degree and executable checks

Keep the parent's `L=m+18` or `L=2m+10` and `nu=1+chi`. The exact
degrees of the new SOS polynomials are

    four computed fields: 20nu L+48,
    six computed fields:  nu(44L+6m+90)+50.         (15)

To check the highest forms, use the parent's stars

    q*=16(P*)^L, s*=2*odd_half,
    P*=P if supplied,
    P*=8*(alpha*x+height_slack)*sum_e Ehat_e if computed.

The index factor has the unique highest term

    four: Nk*=−h*w*s*(q*)², degree 2nu L+3;
    six:  Nk*=−r*=−16^4 H2(P*)^(3L+m+15),
          degree nu(3L+m+15)+1.

Multiply this by the explicit highest form of the parent's four-unit
residual in its Section 4. The product is nonzero and strictly dominates
every retained residual. Its square is therefore the exact highest
form of the new SOS, proving (15). No Boolean or Pell equation is used
to reduce polynomial degree.

The checker verifies the actual gate rewrite, every residual and the
full numerical SOS on 1,280 assignments across 20 variants, including 320
signed assignments. Each variant gets an exact weighted offset audit
of the certificate's residual polynomials, including Nk's degree and
leading coefficient; the degree and leading coefficient of the SOS
follow from its largest residuals and their noncancelling leading
squares. The receipt stores 20 compact ledgers and one complete source.

Another 1,568 weak-checksum packings test the pretyping inequalities for
both signs, and 1,152 independently evaluated Pell cases test the exact
duplication identity and the negative-index ratio contradiction. These
are finite supplements to the parametric proof; they do not materialize
full matrix-history Pell witnesses or prove typing by enumeration.
Run the checker normally for receipt comparison or with `--write` to
regenerate it. Earlier packets remain unchanged.

Author receipt generation and the full default replay pass all 20
ledgers and degree audits. The root and another independent reviewer
passed the full proof and source without findings. The separate review
re-read the original rank and half-index proofs, checking that every
needed strict bound is recovered before typing. Its additional checks
covered 183,521 weak-checksum packings, 4,068 bootstrap boundary cases,
2,304 exact Pell duplication cases, and 512 arbitrary signed full-source
and SOS substitutions across all eight option combinations.
