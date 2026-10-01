# The joint scalar bound shares the native unit product

The [port-bias strong-unit compiler](group_projective_port_bias_folding.md)
can absorb its joint scalar comparison into the existing unit product,
saving **one literal addition**. A strengthened native sign argument
makes the two certificates equivalent on exactly the same strictly
positive supplied coordinate vectors.

The illustrative ten-letter result is **277=117M+160A polynomial
operations, six comparisons and 42 positive witnesses**, with exact
degree **3504**. Its certificate costs 260 operations. The ordinary
input, fixed program numerals, all typing obligations and the complete
fixed-table relation are unchanged. The universal numerical matrix
alphabet is still uninstantiated; the separate numerical 75/88
frontiers do not change.

The new equivalence is a positive-domain theorem. Unlike the preceding
modular strong-unit merge, it is not asserted on unrestricted signed
zero sets. All off-zero source identities below remain exact over the
integers.

## 1. A two-gate replacement for the joint comparison

Write the existing joint-bound register as

    G=sum_(i=0)^3 H_i +sum_(j=0)^7 Zhat_j +beta,
    beta=selection__bound_global>0.

The parent compares G=P+1. Its paid native product U is named
`seven_units`. Append two gates

    L=G-P,           one subtraction,
    Unew=U*L,        one multiplication.                     (1)

Replace U=1 by Unew=1 and remove G=P+1. No supplied coordinate is
removed, added or reparametrized. The existing certificate prefix is
unchanged instruction for instruction.

The output remains an unsquared unit times a positive outer factor:

    F=Unew*(1+sum_remaining_outer R_i^2)-1.                 (2)

For integer supplied assignments, F=0 iff Unew=1 and every remaining
outer residual is zero. The proof below shows that, on the positive
domain, Unew=1 also forces U=L=1. Thus the deleted comparison is
restored with its original positive beta.

## 2. Pretyping bounds for either possible joint sign

An integer product U*L=1 forces U,L to belong to {-1,1}. Write
L=epsilon_J. If necessary, temporarily restore the old joint-bound
coordinate by

    beta_old=beta+1-epsilon_J>0.                           (3)

The source audits that beta has just one consumer: the sum defining G.
Thus (3) changes no native field, history, port, scale, product or
other comparison. It restores exactly G_old=P+1. This is a proof
substitution used before typing; no arithmetic gate or new witness is
being supplied for free.

Equivalently, the two original scalar bounds follow directly. If
Hsum=sum H_i and Zsum=sum Zhat_j, then

    P=Hsum+Zsum+beta-epsilon_J>=12,
    P-Hsum=Zsum+beta-epsilon_J>=8,
    P+1-Zsum=Hsum+beta+1-epsilon_J>=5.                    (4)

Therefore the parent's complete pretyping argument remains valid for
both joint signs. In particular the reconstructed native fields satisfy

    Fi>0,   sum Fi=q-1,   Fi<q,
    F0=1, F1=4, F2=2, F3=8 mod16,
    r=F0+qF1+q^2F2+q^3F3,
    q^3+q^2+q+1<=r<q^4, q>=16.                         (5)

These are scalar inequalities and polynomial residue identities, not
Boolean field typing. The computed checksum is identically +1. Its
fields can be reconstructed for the proof from the factored index
without materializing eliminated runtime registers.

The [shifted-X definition](group_projective_shifted_X_quotient.md)
still gives X=q(w+S)>r unconditionally, where r=(q-1)S. Also
Y=sq>=q, s=2*odd_half+1 is odd, and the two ratio slacks give

    kY<c<k(Y+1),        E=XY>2r+3.                         (6)

These facts require neither the flow equation nor the decoded selector
words. In the computed-P option, (4) restores J>0 from its existing
repunit definition exactly as in the parent.

## 3. Native signs without using the product's sign

The native product U contains the first, main and auxiliary norms,
the strong unit N4, and the index and linear units Nk,Nl. The first
three norms cannot equal -1 modulo four. The same unconditional
exclusion for N4 was proved in the
[strong-unit packet](group_projective_strong_unit_product.md).
Since U is a unit, all four of these factors equal +1. In particular
the full strong equation is restored before the next step. Put

    Nk=epsilon_k, Nl=lambda, epsilon_k,lambda in{-1,1},
    K=k-hE=r+epsilon_k, Jnew=2K-lambda.

Here there is no assumption that epsilon_k=lambda. The only initial
sign relation is U=epsilon_k*lambda=epsilon_J.

The individual bounds and rank proof in
[coupled-linear Sections 2-3](group_projective_coupled_linear_unit.md#2-bounds-before-any-native-typing)
apply unchanged through recovery of lambda. Their hypotheses use only
(5)-(6), the positive native coordinates, the three norm equations and
the restored strong equation. For clarity, their intermediate bounds
are

    r>=4369, 2r-3<=Jnew<=2r+3<E,
    k=psi_(2XY^2+1)(n), n=K modE, n>=r-1,
    c=psi_(a+2)(p), p>n,
    c>A*Delta^2, c>2p, c>Y(r-1)>2(2r+3).

They ensure that the strong-rank lemma yields f>2c before the signed
expression V=of-c is classified as a positive Pell root. The signed
half-index congruences then give

    p=Jnew=2K-lambda,      n=K.

If lambda=-1, p=2n+1. With Q2=chi_A(2)>2XY^2+1 and
2A>Y+1, Pell doubling gives

    psi_A(2n)=2A*psi_Q2(n)>=2Ak>k(Y+1),

contradicting the ratio upper bound for c=psi_A(2n+1). Therefore

    Nl=1,        p=2K-1, n=K.                             (7)

This argument precedes any sign recovery for Nk or L. It does not
invoke the complete field-typing theorem or its checksum conclusion.

## 4. The negative index sign contradicts exact binary population

Suppose epsilon_k=-1. Then K=r-1. Define the proof parameter

    r'=r-2.

The raw native equations now have exactly their original form at r':

    k=r'+1+hE,        p=2r'+1, n=r'+1,
    V=jc-(2r'+1).

All other native quantities are unchanged. The positive inverse map
for the first-root gap restores its original triangular norm. Thus
all ten raw 43-operation kernel equations hold at r'. No claim is
made that any four fields partition a word at this new index.

The elementary bounds needed for the direct binary recovery hold:

    r'>=q^3+q^2+q-1>q>=16,  r'>156,
    X>r>r', Y>=q, a=Y(X+1)>2r'+1,
    q divides X,       Y/q=s is odd.                       (8)

Also r'=15 mod16 is odd. Apply only the ratio, exponent and valuation
argument from
[native binary selector Sections 3-4](native_controller_binary_selector56.md#3-lower-ratio-first-then-the-direct-binary-exponent).
That argument uses the raw equations and (8), not a checksum or field
packing at r'. It gives

    X=2^(2r'+1),       q=2^t,
    Y=binom(2r',r')+sum_(j=1)^r' binom(2r',r'+j)*X^j,
    popcount(r')=t.                                       (9)

To make the dependency explicit, the ratio first gives Y>=X^r'. Its
upper error and the main exponent congruence then recover the displayed
X. Divisibility q|X recovers q as a power of two. Since q<r', X is
divisible by 2q. The binomial formula and the **odd** quotient Y/q
then give the exact valuation v2 binom(2r',r')=t, which equals
popcount(r'). Merely knowing q divides Y would not suffice.

Now return to the original positive fields, still packed at r. By
Fi<q and q=2^t, their base-q blocks do not overlap, so

    popcount(r)=sum_i popcount(Fi)
               >=popcount(sum_i Fi)=popcount(q-1)=t.       (10)

This is only population subadditivity; it assumes no one-hot typing.
Since r=1 mod16 and r>1, put j=v2(r-1)>=4. Writing
r=2^j v+1 with v odd gives the exact identity

    popcount(r-2)=popcount(r)+j-2>=popcount(r)+2>=t+2.      (11)

Equations (9) and (11) contradict each other. Hence epsilon_k=+1.
Together with (7) and the four norm/strong signs this proves U=1.
Then U*L=1 forces L=1.

Every positive new zero is therefore a parent zero on the very same
coordinate vector, with G=P+1 and its original beta. Conversely every
positive parent zero has U=L=1 and is a new zero. The temporary bound
lift (3) was used only to bootstrap the inequalities; there is no
additional branch of positive solutions and no change to the ordinary
input or its program constants.

## 5. Exact counts and degree

Keep the previous notation

    C=3m+3h+p+185+f_flow-3min(h,3)-epsilon,
    L_scale=m+18 if epsilon=0, L_scale=2m+10 if epsilon=1,
    nu=1+chi,

and let b_save be the actual paid port-bias saving. The symbol L_scale
here is the power exponent called L in the parents; the unit L in
(1) is unrelated.

The new certificate adds 1M+1A and loses one comparison. Its finalizer
therefore loses 1M+2A, giving a net saving of exactly one addition:

| Quantity | Exact value |
|---|---:|
|Certificate operations|C+3-b_save|
|Comparisons|7-chi|
|Positive witnesses|m+27-chi|
|Final polynomial operations|C+23-3chi-b_save|

For the illustrative ten-letter table, b_save=1:

| Mask reuse | Computed P | Certificate | Polynomial | M | A | Equations | Positive witnesses | Degree |
|---|---|---:|---:|---:|---:|---:|---:|---:|
|No|No|261|281|119|162|7|43|1486|
|No|Yes|261|278|118|160|6|42|2928|
|Yes|No|260|280|118|162|7|43|1774|
|Yes|Yes|260|277|117|160|6|42|3504|

The old source prefix is unchanged, and the degree of the new linear
unit is nu. Its highest form is

    -P*                         if P is computed,
    sum H_i+sum Zhat_j+beta-P    if P is supplied.

Both are nonzero. The remaining outer highest form is unchanged:
the removed joint residual had degree nu, strictly below the maximal
outer history degree, including the idle-only supplied-P exception.
Thus the old exact degree increases by nu, with highest form equal
to the old highest form times the displayed unit highest form:

    deg F=nu(36L_scale+7m+106)+38+2d,

where d=3 if P is computed or the macro list is nonempty, and d=2
otherwise. This is an operation/degree tradeoff, not a degree reduction.
No equation is substituted into the literal source to lower its degree.

## 6. Source audit and evidence

The [source](group_projective_joint_bound_unit.py) checks the exact
joint sum, paid P+1 and sole consumer of beta. It preserves the full
parent prefix, appends the two gates in (1), and audits the resulting
comparison list and multiplication/addition ledger. All fixed-numeral
multiplications remain paid.

The [receipt](group_projective_joint_bound_unit.json) stores ten compact
ledgers and one complete certificate plus finalizer. Across 640
assignments, including 160 signed assignments, it independently
reconstructs the joint unit, compares every retained register and
residual, and checks the complete final product. These are exact
source identities; unrestricted signed zero-set equivalence is not
inferred from them.

There are 128 structured positive off-zero fixtures with both joint
signs. They check (3), every unaffected parent register, positivity of
all four reconstructed fields, their checksum and residues, and the
native X/r bounds. No native norms are claimed to vanish in these
fixtures. Another 6,945 exhaustive small padded-checksum examples
verify (10)-(11). The raw Pell recovery in (9) is justified by the
parametric proof, not by these finite population checks.

Ten exact weighted-offset polynomial audits check the new unit and
remaining outer factor. The unchanged native product degrees and
highest forms are inherited from the reviewed parent prefix. Its
new final multiplication is then audited by nonzero degree and leading
coefficient multiplication, without expanding a large redundant
output. Normal execution compares the deterministic receipt;
`--write` regenerates it.

Two independent full proof/source reviews and fresh default replays passed
without findings. The reviews checked the pretyping bound lift and the
order of native sign recovery, especially the use of only the raw
ratio/exponent/valuation argument at r-2. Another 2,048 population cases
through q=2^300 and 320 positive fixtures with both joint signs checked
field positivity and complete lift/output identities. These fixtures
remain off-zero algebraic checks, not materialized Pell solutions.
