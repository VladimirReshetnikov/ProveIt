# Positive deterministic Pell comparison centers and pooled self-sized digits

## Endpoint and inherited boundary

The new natural equation is a fixed sum of squares of 172 explicit quadratic
integer residuals in 221 nonnegative unknowns. A sparse companion has 222
unknowns and 173 residuals. The complete coefficient files and independent
contraction certificates are supplied separately. The proof below establishes
existence-equivalence with the raw semantic-anchor source of the incoming
`ConZFC_Cofinal_Anchors_Height_One_Round17_2026-10-25` package. That source's
ordinary proof composes its C222 proof-calculus interpretation with the retained
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation` interfaces. Hence all
new equations have no natural zero iff Con(ZFC), by a proof formalizable in
ZFC. No assertion of consistency, optimality, worldwide priority, or a fresh
complete proof-assistant formalization is made.

The four changes are: pooled equal-denominator bounds in the self-sized radix;
removal of a semantically redundant factorial-digit output bound; a new positive
polynomial Pell comparison center replacing its two freely chosen congruence
parameters; and exact nonnegative monic elimination. Equal-denominator pooling,
the one-row semantic anchor, and alignment K=x are inherited ideas. The positive
center below is a separate construction inspired by the signed negative center
in `ConZFC_Certificate_Reductions_2026-10-25`; it keeps all variables natural and
does not invoke that packet's signed index theorem.

## 1. Positive polynomial center lemma

For integer A>=2 write X_h(A),Y_h(A) for the Pell polynomials determined by

    X_0=1, Y_0=0;
    X_(h+1)=A X_h+(A²-1)Y_h, Y_(h+1)=X_h+A Y_h.

The old indexed-Pell certificate has a principal pair (x,y), an auxiliary pair
(u,v), comparison pair (s,r), and natural witnesses d,e,f,g,hq:

    x²-(A²-1)y²=1,
    u²-(A²-1)v²=1,
    s²-(C²-1)r²=1,
    C=1+4y(d+1),       v=y²(e+1),
    C=A+uf,            s=x+ug,          r=H+4y hq.

The inherited one-index criterion requires H<=y; the retained one-row cap
already implies this inequality before interpreting the index. H>=2 follows
from the raw semantic label polynomial. Thus y>=2 holds at this stage.

Replace the two definitions of C and the auxiliary multiple by

    v=2y²(e+1),
    T=u²,
    C=A+(4y+1-A)T,                                    (PC)

retaining all three Pell norms, s=x+ug, r=H+4y hq, and the complete one-row cap.
The polynomial graph uses a natural coordinate Cminus1=C-1 (already present in
the parent) and the one new square wire T; therefore it asserts C>=1.
Every emitted row is quadratic; the displayed T is one quantified gate variable
at the raw stage, not unaccounted notation.

### Soundness by explicit restoration

The auxiliary norm and v=2y²(e+1) imply

    T-1=(A²-1)v²=4(A²-1)y⁴(e+1)²,   T>A.

Put L=4y+1-A, an integer. If L<0 then L<=-1 and C=A+LT<=A-T<0,
contradicting C>=1. Hence L>=0 and C>=A>=2. Also

    C-1=4yT-(A-1)(T-1),

so 4y divides C-1. Since C-1>0, the old d=(C-1)/(4y)-1 is a natural
integer. The old f=Lu is natural and satisfies C=A+uf. The old auxiliary
multiplier is restored by e_old=2e+1. All other old rows are unchanged.
Thus every zero of the modified raw graph restores a zero of the parent's
full indexed-Pell certificate, without presupposing y=Y_H(A).

For a fully polynomial restoration of d one can use

    d=T-(A-1)(A²-1)y³(e+1)²-1.

Its nonnegativity is a consequence of the retained equations, not a claim of
coefficientwise nonnegativity on all free natural tuples. This restoration
is used in the ordinary existence proof, not passed off as an unconditional
monic-contraction certificate.

### Constructive completeness

Given the parent's decoded canonical principal pair x=X_H(A), y=Y_H(A)
with H>=2, one has y>=2A. Choose a positive Pell auxiliary index ell such that
v=Y_ell(A) is divisible by 2y². Such ell exists: the integer recurrence matrix
has determinant one modulo 2y², so it acts as a permutation of a finite state
set and a positive period returns (1,0) to itself. Set u=X_ell(A) and
e=v/(2y²)-1>=0.

Now L=4y+1-A>0. Define C by (PC), so C>A, C≡A mod u, and C≡1 mod4y.
Take the comparison pair s=X_H(C), r=Y_H(C). Polynomial base transfer gives
s≡X_H(A)=x mod u, and Y_H(1)=H gives r≡H mod4y. Monotonicity of X_H
on bases >=2 gives s>x; also r>=H. Thus g=(s-x)/u and hq=(r-H)/(4y)
are natural. All changed rows have witnesses, and the one-row cap involves
only the unchanged principal pair, seeds and desired indices. This is a
new auxiliary witness choice, not a pointwise bijection on old auxiliary
coordinates.

## 2. Source parameters and the redundant digit bound

The retained source uses natural coordinates, t=t0+12, the original
Cantor-coded calculus, and the six exact-power meanings

    V0=(F²+1)^t,  N=B^K,  q=(N S)^K,
    D_t=q^t,      D_y=q^(y_beta+1),    D_x=q^x,
    K=x,         S=1+Cindex+sum(eight positive encoded columns).

Here y_beta is the source's outer beta bound, distinct from the cap ordinate
y in Section 1. The powers are still finite quadratic Pell certificates;
these meanings are established by the inherited frame and one-row cap before
any binomial or factorial interpretation. Pooling changes no output row used
to orient consecutive Pell pairs and no exact-power frame atom.

The factorial ceiling rows are

    V0+B=BF+r_f+1,        B=r_f+s_f+1.

They imply V0+s_f=BF. Since the exact power V0=(F²+1)^t>=1, one gets
B>=1,F>=1. Since t>=12, V0>F², hence BF>=V0>F² and B>F. The source
endpoint x>=F+1 gives K=x>=2. Therefore

    B< B² <= N <= q.                                  (DB)

Thus the old row q=B+o+1 and its private natural witness o can be removed.
Given a zero of the modified graph, restore o=q-B-1>=0 after the exact
powers have been recovered. None of the foregoing argument uses B=binom(...)
or F=t!, so there is no circular appeal to the digit whose bound is removed.
The original factorial bootstrap, binomial interpretation and CRT proof then
continue unchanged. Completeness deletes this private witness.

## 3. Four pooled low-digit budgets with the self-sized radix

The eleven modular numerator requests fall into four equal-denominator groups:

| Group | Requests | Denominator |
| --- | --- | --- |
| t0 | factorial binomial and encoded row index | q^t |
| t | a,b,c,d,derived label J | q^(t+1) |
| y | the two accumulator columns | q^(y_beta+1) |
| x | the two beta quotient columns | q^x |

Replace each group's separate rows D=r_i+s_i+1 by the single row

    D=sum_i r_i+s+1,        s>=0.                       (PB)

The raw modification has a direct soundness map: for every i, restore
s_i=s+sum_(j!=i) r_j>=0. This does not require any power or factorial semantics.
It preserves every old modular output equation.

For completeness the source constructs true witnesses from a finite C222
refutation. All nine positive CRT representatives are chosen modulo N², with
one lifted by N² to make the existing semantic label J dominate twice every
seed index. Thus the source's preexisting cap completeness remains valid.
The self-sized S is then defined, and q=(NS)^K. The source proves

    K=x,   ell(t+1)<F<K,   ell=2^22,
    every independent representative n<S,   J<=S^ell.

For each ordinary representative request with lower index k<=K and each
0<=j<k, binom(n,j)<S^K (zero coefficients cause no problem). For J and
j<t+1 one similarly has binom(J,j)<=S^(ell*j)<S^K. The only remaining
upper index is n0=F²+t. On these true completeness witnesses F=t!, so
n0>=2t. The coefficients binom(n0,j) are nondecreasing for 0<=j<=t, and

    binom(n0,j)<=binom(n0,t)
                =product_(i=1)^t (F²+i)/i <= (F²+1)^t=V0.

The ceiling rows give V0<=BF<B²<=N. This completeness estimate does not
enter the earlier soundness bootstrap.

Every group therefore has all low-digit coefficient sums bounded by

    5 S^K + N.

This deliberately overcounts the actual groups (at most five requests, and
the factorial appears only in a two-request group). Since K>=2, B>=2,
N=B^K>=4, and S>=2, one has N^K-5>=N. Hence

    5 S^K+N < N^K S^K=q.

The strict bound follows from S^K>1. All quantities are integers; every coefficient sum is at most
q-1. (This estimate uses only complete witnesses, where the inherited
factorial interpretation is already justified.)

Writing the canonical low remainder as

    r_i=sum_(j=0)^(k-1) binom(n_i,j) q^j,

the coefficient-sum bound gives sum_i r_i<=q^k-1. Thus the unique group
slack s=D-1-sum_i r_i is natural and (PB) has a witness. The unchanged
common-root Pell congruence gives these same canonical low remainders in
all original modular output equations; their quotient signs remain those
of the inherited construction.

No aggregate representative bound is introduced. The proof uses precisely
the existing self-sized radix, so the reductions are compatible with K=x
and the cofinal semantic anchor.

## 4. Full proof order

Soundness first restores the deleted private remainder slacks using (PB).
The raw growth frame gives A>=2 and the one-row cap gives y>=H>=2. Section 1
then restores the entire old full-index certificate with natural witnesses.
The unchanged frame, output incidences and one-row cap recover every exact
power. Section 2 restores the removed digit output bound. At this point a
zero of the complete original raw source has been reconstructed, so its
ordinary arithmetic, C222 and ZF/ZFC calibration gives a finite ZFC refutation.

For completeness begin with a finite refutation and use the original
canonical semantic choices, CRT lift, self-sized radix and growth frame.
Section 3 chooses the four new group slacks. Choose a common-root-compatible
base A exactly as in the parent, and take its canonical principal and seed
Pell pairs. Section 1 chooses fresh auxiliary and comparison pairs satisfying
the positive polynomial center. The original one-row-cap witness is unchanged.
Delete the now unused output-bound witness. All other rows are inherited.

Finally every certified monic elimination restores an integer polynomial
nonnegative on the entire remaining natural orthant, with an exact rational
sum-of-squares plus nonnegative-monomial certificate. Independent replay
checks each restoration, every substitution, quadratic degree preservation,
and the complete collected sum of residual squares. These finite checks
verify the literal objects and transformations; the unbounded mathematical
argument above supplies the source equivalence.

The resulting 221- and 222-variable ordinary quartics have exactly the
requested ZFC-provable no-zero equivalence, relative to the identified
inherited logical calibration. Named Pell sequences, factorials, binomials
and powers appear only in this proof, never as primitives of the final
coefficient data.
