# Complete prescribed AND80 from native index and linear units

The [native norm-unit AND83](native_binary_norm_units.md) has a complete
**80=43M+37A** successor, with **72 certificate operations, three
comparisons and15 positive witnesses**. Its product finalizer has total
degree **at most124**. The same-cost SOS finalizer has degree at most244.
An index-only intermediate costs82 and preserves the parent's exact
supplied positive zero set. The coupled80 form preserves every outer
coordinate through a conditional normalization of private native fields;
it is not a bijection on all supplied positive tuples.

The [source](native_binary_index_coupled_units.py) and
[receipt](native_binary_index_coupled_units.json) also apply the same
proved rewrite to the packed motion, toggle and fixed Wang-program
hosts. No universal Wang table or ordinary TM input morphism is supplied.
These component savings do not change the75/87 universal route or the
separate numerical U9 compiler.

## 1. Host contract and literal factors

The input packet must already be a complete prescribed positive AND
embedding of the norm-unit parent, with its actual native rows and
comparisons. In every emitted host, before equations,

    q=16S>=16, S>=1,
    F0,F1,F2,F3>0,
    padded_A=12 mod16, padded_B=10 mod16, F3=8 mod16.

For standalone AND, S=P is supplied positive and the padded ports are
16Hhat-4,16Mhat-6,16Zhat-8. In folded hosts the unpadded words are
nonnegative and the same ports are16H+12,16M+10,16Z+8. The parent's
positive-domain proof is part of the host contract; multiplication by16
alone is not a proof that an arbitrary caller's scale is positive.

The four- and six-computed-field options and both strong forms remain
available. Write

    X=wq, Y=sq, E=XY, a=Y(X+1), A=a+2, Delta=A^2-1,
    k=eta+zeta, c=kY+eta,
    r=F0+qF1+q^2F2+q^3F3,
    Jtarget=2r+1, U=jc-Jtarget, V=of-c.

Supplied positive ratio slacks give kY<c<k(Y+1). A supplied c or r
retains its defining comparison. With positive-scale substitution,
X=q(r+beta)>r. Without that substitution the retained comparison is
X=r+beta>r. No index or checksum conclusion is used in this bound.

The norm-unit parent has the factors

    N0=g^2+4XY^2 k(g-k),
    N1=d^2-Delta*c^2,
    N3=W*(U^2-y^2)+y^2,
    Qc=q-(F0+F1+F2+F3).

For ordinary strong form W=Delta*(f^2-1), and the comparison
(ic^2)^2=W remains. For normalized strong form
W=Delta^2*(ic^2)^2 and Ns=f^2-Delta*(ic^2)^2 is another unit factor.
All first, main, auxiliary and present strong factors exclude-1 modulo4:
Delta is0 or3; the ordinary W is0 or1, and normalized W is a square.
The auxiliary sign argument works for either U or V without first
assuming either expression positive.

Whenever Ns=1, i_old=Delta*i restores the full ordinary strong equation.
Thus in either form the later rank proof uses the full relation

    T=i_old*c^2>0, T^2=Delta*(f^2-1).                (1)

There is no relaxed divisibility assumption.

## 2. Bounds and the common rank argument before typing

At an integer-product zero, every factor is an integer unit and every
retained ordinary comparison holds. The independent mod4 exclusions
make all norm factors+1. Until the linear signs are recovered, allow
Qc=+1 or-1. Positivity and the exact packing alone then give

    q^3+q^2+q+1 <= r
       <= (q-2)q^3+q^2+q+1 < q^4,
    r>=4369, Y>=q>=16,
    E>2r+3, Y(r-1)>2(2r+3).                        (2)

For the upper packing bound, allow the larger sum q+1, put one unit
in each lower field and put the remaining mass in F3. No bit typing,
dyadic conclusion or range decoding is assumed.

The positive first-root inverse from the parent gives the triangular
Pell equation and hence

    k=psi_Pfirst(n), Pfirst=2XY^2+1, n>=1.

Since Pfirst=1 mod E, k=n mod E. The new index factor below permits
K=k-hE=r+epsilon, epsilon in{-1,1}. As0<r+epsilon<E, n>=r-1.
The main norm gives c=psi_A(p),d=chi_A(p), p>=1. Since Pfirst>A and
c>k, monotonicity forces p>n, hence p>=r. Ordinary Pell growth gives

    c>A*Delta^2, c>2p,
    c>Yk>=Y(r-1)>2(2r+3).                          (3)

These are the actual large-index hypotheses; none comes from a presumed
positive checksum.

The integral-rank and divisibility argument in
[the relaxed auxiliary proof](../../1980/PELL_RELAXED_AUXILIARY_PROOF.md)
applies to(1), A>1 and c=psi_A(p)>A*Delta^2. It gives

    f=chi_A(m), c divides m, T=Delta*psi_A(m),
    m>=c>2p.                                      (4)

The argument is stated for a general Pell parameter A; its historical
source's a+4 notation imposes no restriction on the present A=a+2.
For clarity, the needed rank step uses c^2 dividing T, the large bound
in(3), strong divisibility of psi and the doubling inequality. It
cannot be inferred merely from the main norm without(1).

Suppose the auxiliary argument is Z=jc-Jnew=of-c, where
0<Jnew<=2r+3. It is positive: for U use c>2Jnew; for V first use
f>chi_A(2p)=1+2Delta*c^2>2c and o>=1. Its unit equation is

    (TZ)^2-(T^2-1)y^2=1.

As T>1 and y>0, Pell classification gives an odd ell=2v+1.
The integer odd-index polynomial yields

    Z=(-1)^v psi_A(ell) mod f,
    Z=(-1)^v ell mod c.

Together with Z=-c mod f and Z=-Jnew mod c, the chi-doubling and
signed step-down argument used in the
[index-unit proof, Section3](group_projective_index_unit.md#3-recovering-the-main-index-from-the-unchanged-strong-equations)
gives ell=+p or-p mod m. Equation(4) then gives Jnew=+p or-p mod c.
The strict0<p,Jnew<c/2 bounds exclude the negative representative and
all nonzero multiples of c. Consequently

    p=Jnew.                                       (5)

This cites the individual rank and signed-index lemmas with their
hypotheses verified here. It does not invoke a complete AND theorem
while its checksum remains signed.

## 3. The index-only saving preserves all positive zeros

Retain U=V. Replace k=r+1+hE by the factor

    Nk=k-hE-r,

and multiply Nk into the existing product. At a zero the signs obey
Qc=Nk=epsilon, all norms+1. Apply(5) with Jnew=2r+1. Since n<p<E,
the congruence n=r+epsilon mod E identifies n=r+epsilon exactly.
If epsilon=-1, p=2n+3.

Put Q2=2A^2-1. Direct substitution gives Q2>Pfirst and2A>Y+1.
The exact duplication identity and monotonicity imply

    psi_A(2n)=2A*psi_Q2(n)>=2Ak>k(Y+1).

Then c=psi_A(2n+3) contradicts the upper ratio. Therefore epsilon=1.
The checksum and index comparison both recover their original signs;
all parent positive zeros are restored in the same supplied coordinates.
The converse is immediate: every parent zero has Nk=1.

Literally, reuse the private register R11 as K=k-hE instead of
(r+1)+hE, then add Nk=K-r and a product multiplication. The first
replacement has unchanged cost. The certificate adds1M+1A and removes
one comparison, saving exactly1A in either complete finalizer.

## 4. Coupling saves two more operations and preserves the outer relation

Now replace the auxiliary square U^2 by V^2 and add

    Nl=V-jc+2K.

Delete U=V and multiply Nl into the product. At a zero write
Nk=epsilon,Nl=lambda. All norms are+1 and Qc=epsilon*lambda.
Set Jnew=2K-lambda; then2r-3<=Jnew<=2r+3. Equations(2)--(5) apply,
and give p=Jnew and n=K exactly. If lambda=-1, then p=2n+1,
contradicting the same strict duplication/upper-ratio inequality.
Hence

    Nl=1, Qc=Nk=epsilon, p=2K-1, n=K.              (6)

The index sign is intentionally not excluded. If epsilon=1, the old
index and auxiliary comparisons are already restored. If epsilon=-1,
the retained padded input comparisons give

    F3=8, F1=4, F2=2 mod16,
    F0=3 mod16,

because sum Fi=q+1 and q=0 mod16. Thus F0>=3. Define only

    F0_old=F0-2>0, beta_old=beta+2>0,
    r_old=r-2>0.                                  (7)

When r is computed, its actual packed register recomputes r-2; when
supplied it is changed explicitly. All other supplied coordinates stay
fixed. The X bound remains true: r_old+beta_old=r+beta both for the
ordinary bound and for X=q(r+beta). Thus X,Y,k,a,c,d and every strong
factor keep their values. The new checksum is+1, while
K=r-1=r_old+1 and

    jc-(2r_old+1)=jc-(2K-1)=V.

The old auxiliary norm and its linear comparison recover exactly.
Every retained native/outer equation holds. The unchanged padded ports
therefore satisfy the full old complete prescribed AND relation.

The source audits private F0 and beta consumers, all supplied-r uses,
transitive outside-core dependencies, scale/input-port independence and
recursive declared exports before permitting(7). No history, input,
program, duration, scale or supplied outer parameter changes. These are
necessary host guards; an arbitrary outer constraint involving a
changing native coordinate is not accepted by the helper.

Conversely every parent positive zero enters with Qc=Nk=Nl=1 and the
same native tuple, so it satisfies the coupled source. This proves
accepted-outer equivalence including fresh positive native extension.
The conditional map(7) is not asserted injective or an off-zero graph
bijection. No new negative-branch full zero is claimed by finite tests.

Literally delete r1=r+1, tr1=r1+r and U=jc-tr1. Replace their three
additions/subtractions with K+K,V-jc and their sum Nl. The existing H2
square takes V as both operands. One extra product multiplication and
one removed comparison save2A in either finalizer.

## 5. Exact source identities, guards and ledgers

The public API is `rewrite(old,coupled=True)`; `index_rewrite(old)`
exposes the intermediate and `couple(index_packet)` applies just the
second step. `build` emits standalone AND, motion, toggle and literal
fixed-program examples. The native-parent reconstruction checks every
actual core row, all core comparisons, computed aliases and the factor
list before rewriting. Additional local checks audit private register
consumers and recursive dictionary/list/tuple interface leaves.

On arbitrary integer assignments the index factor is

    Nk=1+old_index_residual.

For the coupled step, with old linear residual Rlin=U-V and the actual
paid ordinary or normalized coefficient W,

    N3_new=N3_old+W*(V^2-U^2),
    Nl=2Nk-1-Rlin.                                 (8)

Every other retained residual agrees. The checker reconstructs the whole
new product from these corrected factors and checks both finalizers;
it never divides by a factor or assumes an off-zero Pell equation.
The full old and new polynomials are not claimed identical off zero.
On the conditional locus Qc=Nk=epsilon,Nl=1, restoration(7) does give
an exact complete-output identity with the immediate index parent.

For a norm-unit parent with certificate C and e comparisons, index-only
has C+2,e-1; the coupled form has C+3,e-2. Positive witness counts are
unchanged. Both finalizers cost3e-1 beyond the certificate, so their
net savings are1 and3 respectively. Every numerical multiplication,
including all padding and the first-root coefficient4, remains paid.

The following emitted schedules use six computed fields, positive scale
and normalized strong units. Program rows use the parent's illustrative
six-instruction literal-input program, not a universal program.

| Host/form | Certificate | Polynomial | Comparisons | Witnesses | Product degree bound |
|---|---:|---:|---:|---:|---:|
|AND, index|71|82=43M+39A|4|15|124|
|AND, coupled|72|80=43M+37A|3|15|124|
|Motion, index|195|215=94M+121A|7|28|2156|
|Motion, coupled|196|213=94M+119A|6|28|2020|
|Toggle, index|112|129=60M+69A|6|21|792|
|Toggle, coupled|113|127=60M+67A|5|21|748|
|Wang program, index|316|351=151M+200A|12|40|5897|
|Wang program, coupled|317|349=151M+198A|11|40|5503|
|Computed-action Wang, index|309|332=147M+185A|8|36|5897|
|Computed-action Wang, coupled|310|330=147M+183A|7|36|5503|

All degree claims are conservative bounds on the actual emitted source.
The inherited guarded cancellation of a^2*c^2 in the main norm remains
an ordinary polynomial identity. The actual changed auxiliary square
and added factors receive fresh propagation. The product bound is the
sum of factor bounds plus twice the largest remaining residual bound;
the SOS bound is twice their maximum. No zero-set relation lowers degree.
For standalone80 the factor bounds are18,48,11,1,28,8,8, summing122;
the remaining two input residuals have degree1, giving124 and244.

## 6. Reproducible evidence and scope

Run `python3 native_binary_index_coupled_units.py` for receipt comparison.
The source emits52 ledgers:48 basic host/scale/field/strong/coupling
choices and four fixed-program examples. It checks1,248 assignments,
624 signed, yielding2,496 complete factor/residual/finalizer identities.
Every paid gate reaches each selected output. A nested private export
is explicitly rejected.

Another648 signed-checksum packing fixtures check the pretyping bounds,
and384 exact Pell evaluations check the duplication inequality. The128
conditional restoration fixtures cover both signs, both scale options,
both field options and both strong forms;64 use the negative index sign.
These impose the displayed linear/checksum conditions only. They are
not full numerical Pell zeros. The complete positive theorem follows
from Sections2--4 and the parent extension theorem.

Author receipt generation and a fresh default replay pass. A separate
author check evaluated32 complete polynomial affine slices across all
sixteen standalone scale/field/strong/coupling choices and both finalizers;
each actual slice degree is within its stated bound. All five local links
resolve.

Two independent full proof/source/fresh-default reviews pass without
findings. Both checked the actual rank hypotheses, signed step-down and
conditional positive restoration against the cited lemmas. The root's
separate original-norm-parent oracle checked1,040 assignments,520 signed,
across all52 schedules, reconstructing both added factors, the auxiliary
square correction, retained residuals and both finalizers. The second
reviewer's independent literal executor and manual original-parent
factors checked416 assignments,208 signed, across all52 schedules,
yielding832 complete factor/residual/finalizer identities. Neither
review modified source or receipt, and neither calls finite fixtures
complete Pell zeros.
