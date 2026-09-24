# Boolean dummy bits can control the packed index modulo a power of five

Let d and N be positive powers of5, with **N>25d**, and put

    B=2^d, M=dN, T=N/5.

Every residue modulo M is a sum of a subset of the distinct weights

    B^(4j), 0<=j<T, together with the optional weight B.            (1)

Every weight is used either zero or one times. This is an exact finite
subset statement, not a signed-digit or unrestricted multiplicity claim.
The constructive proof below also places all selected cells far enough
from the end of a word to avoid wrap in two prescribed rotations.

The [checker](../verification/explore_five_adic_dummy_control.py) and
[receipt](../verification/explore_five_adic_dummy_control.json) verify the
construction, independently check finite complete subset coverage, and
check its application to the actual affine packed-index formula. This
lemma claims no complete certificate operation count. Its arithmetic
application states explicitly the compiler properties it needs.

## 1. The powers enumerate the required subgroup

Write d=5^a and N=5^n. Let A=B^4=2^(4d). The elementary valuation formula is

    v_5(A^j-1)=a+1+v_5(j), j>0.                                (2)

Indeed v_5(2^4-1)=1. If v_5(z-1)=s>=1, the binomial expansion gives
v_5(z^5-1)=s+1: its linear term has valuation s+1 and every other
nonzero term has larger valuation. If 5 does not divide t, the same
expansion gives v_5(z^t-1)=s. Iterating these two observations proves (2).

Since M=5^(a+n), formula (2) shows that A has exact order5^(n-1)=T
modulo M. All its powers are1 modulo5d. There are precisely T residues
of that form modulo M. Consequently

    {A^j mod M: 0<=j<T}={1+5d*t mod M: 0<=t<T},                (3)

and the correspondence between j and t is a bijection. Enumerating
these powers is one finite constructive way to invert this correspondence.
No operation of a proposed certificate is assumed to perform that search;
it constructs its existential witnesses.

## 2. Construct a Boolean subset for any target

Fix a target z modulo M. Choose epsilon in {0,1} so that z-epsilon*B
is not divisible by5: use epsilon=0 when 5 does not divide z, and
epsilon=1 otherwise. Let k be its representative modulo5d in
{0,...,5d-1}. Then

    1<=k<5d<T, 5 does not divide k.                           (4)

The strict inequality follows from N>25d. Put

    s=(z-epsilon*B-k)/(5d) modulo T.

This is well-defined using any integral representative of z. Since k
is a unit modulo T, choose t0 satisfying

    k*t0+k*(k-1)/2=s modulo T.                                (5)

Choose the k distinct cyclic consecutive residues

    t0,t0+1,...,t0+k-1 modulo T.

Their distinctness uses k<T. Their sum satisfies (5), so the sum of the
k corresponding residues1+5d*t, plus epsilon*B, is z modulo M.
Use (3) to turn these t residues into distinct j values and hence into
the weights B^(4j). The extra weight B comes from cell1, which is not
one of the cells4j. This proves the assertion with genuine Boolean bits.

## 3. All selected cells can be internal to both rotations

The available cell indices are

    I={4j:0<=j<N/5} union {1},
    max I=4N/5-4.                                            (6)

Suppose N=hH with positive integers h,H and H>=25. Then every i in I
satisfies

    i+1<N, i+h<N,                                          (7)

because h<=N/25 and 4N/5-4+N/25<N. Thus adding a bit in any available
cell causes no end-of-word wrap when multiplying that bit by B or B^h.
The set includes cell0 and may include a marked cell. This is harmless
only when the adjustable bit is an ignored native dummy position,
distinct from every marker selector, as assumed in the application.

## 4. Exact application to a packed index

The following statement is conditional only on the listed compiler facts.
It does not need a prospective smaller certificate as a dependency.

Suppose b,L,h,H are positive powers of5, d=bL, N=hH>25d, H>=25, and

    R=2^b, B=R^L=2^d, q=B^N, D=DC+B*DR+B^h.

Suppose a fixed native position e is an ignored Boolean dummy, initially
zero in every cell. Turning it on in any subset of the available cells
preserves all local predicates, marker slots, and paid masks. Assume the
compiler bounds ensure that the integer field has its intended carry-free
linear value. Denote the baseline content, remainder and field by C0,Z0,F0.
The remainder differs from the content only by unchanged marker terms.

If K is the sum of the selected weights B^i, the dummy change is exactly

    C=C0+R^e*K, Z=Z0+R^e*K, F=F0+D*R^e*K.                  (8)

For the two rotations this follows from (7); the central convolution is
linear by the assumed field layout and bounds. Let the fixed packed mask
word be Qmask and define the actual integers

    r0=(q^2-Z0-qF0)(q^2-1)+Qmask,
    r =(q^2-Z -qF )(q^2-1)+Qmask.

There is then an exact integer identity, not just a congruence,

    r=r0-gamma*K,
    gamma=R^e*(q^2-1)*(1+qD).                             (9)

Consequently 2r+1=(2r0+1)-2gamma*K. The coefficient beta=-2gamma is
a unit modulo M=dN whenever

    2DC-DR is not zero modulo5.                            (10)

To verify this, every power of5 is1 modulo4, so R,B,q and B^h are all2
modulo5. Hence

    1+qD = 1+2(DC+2DR+2) = 2DC-DR modulo5.

Both R^e and q^2-1=3 modulo5 are units. Since M is a power of5,
condition (10) proves the assertion. For any desired residue jstar,
apply Sections1--2 to the target

    K = ((2r0+1)-jstar)*(2gamma)^(-1) modulo M.             (11)

This gives the desired congruence at the **actual changed packed index**.
In particular jstar=d*h gives

    2r+1=d*h modulo dN,
    2^(2r+1)=B^h modulo(q-1),                              (12)

provided the packed-index bounds give r>=0. The final implication uses
2^(dN)=q=1 modulo(q-1); it does not replace the actual r by a formal target.

Condition (10) can be enforced by a compiler's optional unchecked high
monomial R^g in DC: if the old expression is zero modulo5, adding it
changes that expression by the nonzero residue2R^g. This arithmetic
observation does not by itself justify the monomial's layout. Its entire
native translates must lie below the cell boundary and above every tested
field position, and its coefficient mass must be paid in the no-carry bound.

## 5. Order of construction and positive transport quotient

The application has a useful noncircular order. First fix a genuine word,
its spatial width h, height H, and the field for the genuine B^h rotation.
Compute r0, choose the Boolean dummy subset, and compute the actual changed
r from (8)--(9). Only then apply (12). If a later arithmetic kernel supplies
X=2^(2r+1), its rotation agrees exactly with the already chosen B^h rotation.

If the original positive transport quotient z0 satisfies

    (DC+B*DR+B^h)C=F+z0*(q-1),

and X>B^h, the replacement quotient

    z=z0+((X-B^h)/(q-1))*C                                (13)

is a positive integer and satisfies (DC+B*DR+X)C=F+z(q-1). Positivity of
all other witnesses, the existence of the genuine word, preservation of
every mask, and a kernel converse at its actual r remain obligations of
the complete construction using this lemma. They are not inferred solely
from modular subset coverage.

## 6. Exact finite checks and scope

The checker constructs subsets for every target at (d,N)=(1,125) and
(5,625), and independently computes all reachable subset residues by
Boolean dynamic programming. It checks larger power-of-five pairs by
sampled targets, checks the exact valuation and subgroup bijection, and
checks internal-index bounds and the unit-coefficient repair.

Separate moderate integer examples verify (8)--(11) by constructing the
actual changed r and comparing the integer affine identity. These use
illustrative coefficients and are explicitly not full universal compiler
instances or Pell tuples. No actual enormous compiler q with N>25d is
materialized. The general theorem is the proof above, supported by exact
finite checks. The default CLI compares its receipt without writing;
regeneration requires --write. No published certificate source is changed.

Review status: author and independent complete proof/source reviews pass.
Fresh default checks match the saved receipt. Additional independent
checks cover 300 direct modular-power targets on three new parameter pairs.
