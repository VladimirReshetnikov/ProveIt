# A positive first-root gap saves two polynomial additions

The complete [padded-program compiler](group_projective_padded_program_margin.md)
has a successor whose single sum-of-squares polynomial saves **two
additions**. A positive change of its first Pell-root coordinate makes
that norm an integer unit without increasing its definition cost. Joining
it to the existing three-unit product adds one certificate multiplication
and removes one comparison. Both positive ratio slacks, the full strong
auxiliary comparison and every ordinary-input condition remain.

The change is a bijection of complete positive solution tuples, with
one coordinate renamed. All sign and positivity arguments precede native
typing; no power-of-two conclusion is assumed. The alternative that
keeps the new norm separate has the parent's exact cost and lowers the
four-field polynomial degree.

Let the immediate parent's certificate cost be

    C=3m+3h+p+185+f_flow−3min(h,3)−epsilon,

where m=2^h is the padded edge count, p is the paid port cost,
epsilon=1 denotes controller-mask reuse (requiring m≥8), and chi=1
denotes the computed-P variant. Keep its fixed positive compiler
numerals and the compile-time margin `alpha+beta+1≥m`.

| Option | Computed native fields | Certificate | Equations | Positive witnesses | SOS polynomial |
|---|---|---:|---:|---:|---:|
|Separate first norm|a,d,k,s|C|18−chi|m+34−chi|C+53−3chi|
|Merged first norm|a,d,k,s|C+1|17−chi|m+34−chi|C+51−3chi|
|Separate first norm|a,c,d,k,r,s|C|16−chi|m+32−chi|C+47−3chi|
|Merged first norm|a,c,d,k,r,s|C+1|15−chi|m+32−chi|C+45−3chi|

These are complete fixed-table compiler bounds. No numerical universal
alphabet is instantiated, and no improvement to the separate 75/88
frontiers is claimed. The [checker](group_projective_first_norm_unit.py)
and [receipt](group_projective_first_norm_unit.json) contain the exact
rewiring, literal ledgers and polynomial identities.

## 1. A positive coordinate with a modulo-four norm

Use the native kernel's computed quantities

    X=wq, Y=sq, E=XY, V=XY², k=eta+zeta,

with eta,zeta>0. The old triangular equation is

    (E²+X)(kY)²=tau(tau+1),
    equivalently V(V+1)k²=tau(tau+1).               (1)

Replace the supplied positive tau by a supplied positive g, named
`selection__tau_gap`, and define

    N0=g²+4Vk(g−k).                                (2)

Its exact algebraic identity is

    N0=(2Vk+g)²−4V(V+1)k².                         (3)

For arbitrary integers, N0≡g² mod4, so N0 cannot equal −1. This exclusion
does not require positivity, an equation or any typing conclusion.

Suppose first that (1) holds at an old positive tuple. Put

    root=2tau+1, g=root−2Vk.

The equality `root²=1+4V(V+1)k²>(2Vk)²` gives g>0, and (3) gives
N0=1. Conversely, suppose N0=1 with the new positive coordinates.
Then `root=2Vk+g>0`. Equation (3) shows that root is odd and root>1,
so

    tau=(root−1)/2=Vk+(g−1)/2                       (4)

is a strictly positive integer and satisfies (1). The two maps are
inverse. They change no other witness.

The positivity used here is available before native typing. If P is
supplied, P>0. If P is computed, the source has
`P=(B−1)J+1`, `J=sum(Ehat_e−1)≥0`, and B=8D>1 on every positive
assignment, so P≥1. In either case the explicit source computes
`q=16P^L≥16`. Thus X,Y,V,k are all strictly positive independently
of the checksum and norm equations. Both positive ratio slacks are
unchanged; no ratio inequality has been replaced by (2).

## 2. Restoring every merged equation before typing

The immediate parent has the three-factor comparison

    N1*N3*Q=1,
    N1=d²−Delta*c²,
    N3=T²(U²−y²)+y²,
    Q=q−(F0+F1+F2+F3),                             (5)

where Delta=(a+2)²−1 and T=ic². The parent proves unconditionally
modulo 4 that N1 and N3 cannot equal −1. Retain their exact definitions,
including T² in N3, and replace (1) and (5) by

    N0*N1*N3*Q=1.                                 (6)

An integer product 1 has every factor in {−1,1}. The three independent
modulo-four exclusions force N0=N1=N3=1, and then Q=1. The inverse
(4) restores the positive old tau, so every parent equation holds.
Only now invoke the parent's typing, controller, range, history and
ordinary-input theorem. There is no circular appeal to that theorem
to determine a unit sign.

Conversely, any parent positive zero gives the positive g above and
all four factors equal 1. This proves exact positive-tuple equivalence
with the parent. The separate option simply retains (5) and adds the
separate comparison N0=1; it has the same coordinate bijection.

The strong auxiliary equality `T²=Delta(f²−1)` is retained explicitly.
It is neither omitted nor used to replace N3 off its zero set.

## 3. The literal source change and exact off-zero identity

The old first norm has these six private gates, apart from the already
shared kY product:

    tauplus1=tau+1; R9=tau*tauplus1;
    UM2=E*E; coefficient=UM2+X;
    ratio_square=(kY)*(kY); L9=coefficient*ratio_square.

They cost 4M+2A. Replace them by exactly

    gap_square=g*g;
    root_base=E*(kY);
    signed_gap=g-k;
    cross=root_base*signed_gap;
    four_cross=4*cross;
    first_unit=gap_square+four_cross.

These also cost 4M+2A. The numeral4 multiplication is charged. No old
gate outside this list uses a deleted result. The separate option changes
the old comparison L9=R9 to first_unit=1. The merged option adds the
single product `four_units=unit_product*first_unit`, replaces the old
unit-product comparison by four_units=1, and deletes L9=R9.

Thus the merged certificate adds 1M, its comparison count falls by one,
and its positive witness count is unchanged. In the SOS source the added
multiplication is canceled by one fewer residual square. The saving is
exactly the two additions otherwise needed for one residual subtraction
and one term of the sum. No source comparison is free inside the single
polynomial ledger.

For an off-zero identity, let r_first=L9−R9 and
r_unit=N1*N3*Q−1 be parent residuals evaluated under (4). On arbitrary
new supplied assignments, including signed assignments, (4) is a rational
coordinate substitution if g is even. Then

    first_unit=1−4r_first,
    r_merged=(r_unit+1)(1−4r_first)−1.              (7)

All other residuals are identical. The separate SOS is exactly the
parent SOS plus `15*r_first²`; the merged SOS deletes the two old
squares and adds r_merged². These are literal polynomial identities,
not simplifications conditional on old equations. At zeros the sign
argument above proves g odd and restores integer coordinates.

Writing the inherited common-register savings as d_M,d_A, the merged
certificate split is

    M=m+2h+83+f_M−d_M−epsilon,
    A=2m+h+p+103+f_A−d_A.

Its SOS splits are

    four: M=m+2h+100+f_M−d_M−epsilon−chi,
          A=2m+h+p+136+f_A−d_A−2chi;
    six:  M=m+2h+98+f_M−d_M−epsilon−chi,
          A=2m+h+p+132+f_A−d_A−2chi.

The separate option subtracts 1M from the displayed certificate and adds
2A to the displayed SOS. The functions d_M,d_A retain their parent
values; no new table or physical-port optimization is assumed.

## 4. Exact degrees and highest forms

Let

    L=m+18 for the eight-lane mask,
    L=2m+10 for controller-mask reuse,
    nu=1+chi.

Degree is measured in the actual supplied coordinates and ordinary x,
with all compiler numerals constant. The exact degrees are

| Option | Four fields | Six fields |
|---|---:|---:|
|Separate first norm|10nu L+32|nu(32L+4m+60)+38|
|Merged first norm|16nu L+42|nu(38L+4m+60)+48|

The separate four-field option improves the parent's `12nu L+16` at
unchanged cost because nu L≥20. The merged options trade two fewer
operations for the higher degree shown. No equation such as P=B^t is
used when calculating these degrees.

Here is an explicit nonzero highest-form audit. Stars denote highest
homogeneous parts. If P is supplied, P*=P and degP=1. If P is computed,

    P*=8*(alpha*x+height_slack)*sum_e Ehat_e, degP=2.

In either case define

    q*=16(P*)^L, s*=2*odd_half, k*=eta+zeta,
    a*=w*s*(q*)².

The first unit has highest form and degree

    N0*=4w(s*)²(q*)³ k*(g−k*),
    degN0=3nu L+5.                                 (8)

For four computed fields, c,r remain supplied. The main-norm square
terms cancel at their top degree; the two equally high surviving
contributions give

    N1*=8ga*(a*)²*(c+2ga),
    N3*=i²j²c^6,
    Q*=q*.

Thus the three-unit residual has highest form
`T*=N1*N3*Q` and degree5nu L+16. For six computed fields use

    c*=k*s*q*,
    r*=16^4 H2 (P*)^(3L+m+15),
    N1*=8ga*(a*)²*c*,
    N3*=i²(c*)^4*(2r*)²,
    Q*=q*.

Its three-unit residual has degree `nu(16L+2m+30)+19`. These are the
same three-unit highest forms as in the parent; the coordinate g occurs
in none of them.

In the separate option, this three-unit residual strictly dominates the
new first norm and every other residual. Its square (T*)² is the exact
highest form of the SOS. In the merged option, the new residual has
highest form N0*T*, strictly dominates all remaining residuals, and its
square is the exact SOS highest form. All these displayed polynomials
are nonzero. This proves the degree table without assuming cancellation
between different squares.

## 5. Reproducible checks

The checker imports the actual padded-program source, verifies the exact
six deleted instructions, sorts the replacement DAG, and checks both
complete SOS variants under (7). It includes positive supplied tuples
whose computed J is zero, verifying q≥16 before any typing equation.
Off-zero even-g cases deliberately produce half-integral parent roots;
the rational polynomial identity is kept separate from the integral
positive-zero theorem.

The receipt has 40 compact ledgers covering m=2,8,16, both field choices,
both P choices, both merge choices, and the optional controller mask
where m≥8. It includes one complete literal source example. All 40 actual
certificate DAGs receive exact weighted offset residual-degree and
highest-coefficient checks. The SOS degree is twice the largest residual
degree, and its highest coefficient is the sum of the corresponding
leading-coefficient squares; the audit avoids redundantly expanding those
final squares. Separately, 1,280 complete residual/SOS identities include
320 signed cases. Another 64 residue classes check the new modulo-four obstruction, and
384 exact Pell components check both positive coordinate maps.

Run the source normally to compare the deterministic receipt, or pass
`--write` to regenerate it. The parent packets are unchanged. These
finite audits supplement the full positive equivalence proof; they do
not instantiate a universal presentation or materialize full native
Pell extensions for matrix histories.

Author receipt generation and the complete default replay pass all 40
ledgers and degree audits. The root and two other independent reviewers passed the full proof and
source without findings. One separate audit checked 1,152 full-source/SOS
identities over m=2,4,8,16, including 590 half-integral off-zero parent
roots and 48 positive J=0 cases, plus 512 independent positive Pell
coordinate maps. The reviews include the typing-independent positivity,
all unit signs, exact six-gate replacement, both options' counts and all
highest forms.
