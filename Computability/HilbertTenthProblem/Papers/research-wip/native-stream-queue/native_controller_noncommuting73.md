# A paid noncommuting native NAND relation in 73 operations

This is a complete **finite cyclic relation**, costing **73=37M+36A**,
with 21 equations and 27 positive auxiliaries. It uses the reviewed
[54-operation selector module](native_controller_three_selector_53.md).
One NAND input is a full cyclic rotation; the other rotates the tail and
then moves the initial digit to the top. These permutations can fail to
commute on an admitted word. No universal circuit compiler, ordinary-input
initialization or accepting computation is supplied, so this is not a
complete universal certificate below 76.

## 1. Exact source and interface

The selector module has positive parameters q,F0,F1,F2 and proves

    q=3^t, t>=1; H=(q-1)/2; Fi=H+Ti;
    Ti are Boolean ternary words, T0+T1+T2=H;
    the first selected label is 0.

Use its 54-operation version, with positive supplied H. Define

    D=2H-F2=H-T2,          S=H+F2-F0.

D is Boolean, its units digit is 1, and S has trits 0,1,2 according
to the selected label. Thus Boolean words A,B satisfying A+B=S have
D=NAND(A,B) at every position. In particular, the fixed first label
forces both input words to have units digit 0.

Besides q,F0,F1,F2, take R0,R1 as positive parameters. Supply positive
E,Q,C,J,B,K0,K1,Z0,Z1 and impose

    D=3E+1,               q=3Q,
    Q=R0*Z0,              C+J=Q,
    R0*C+(Q-1)=E+(Q-1)*K0,
    A=C+Q,                A+B=S,
    R1*B=D+(2H)*K1,       q=R1*Z1.                     (1)

A is derived, so A=C+Q is an instruction rather than another supplied
coordinate and comparison. The 18 positive auxiliaries of the selector
module plus the nine just listed make 27. All eight new comparisons are
included in the source; together with the selector's 13 they give 21.

The implementation calls H `Hrep`, D `Dword`, S `Sword`, B `portB`,
A `portA`, and J `Jbound`. The tail modulus register has its own name,
so it does not overwrite the Pell kernel's modulus.

## 2. Soundness, including bounds before typing

Since E>0 and D=3E+1 is a length-t Boolean word,

    t>=2, Q=3^(t-1), 1<=E<=(Q-1)/2.

E is exactly D's tail after removing the known units digit 1. The
positive factorization Q=R0*Z0 forces R0=3^a for 0<=a<=t-1. The
explicit positive slack comparison gives

    1<=C<=Q-1.                                             (2)

Reducing the first routing equation modulo Q-1 gives
R0*C=E modulo Q-1. Since R0 is invertible modulo Q-1, it has one
residue solution. The true cyclic right rotation of E by a positions is

    C*=floor(E/R0)+(Q/R0)*(E mod R0).

It is Boolean and lies between 1 and (Q-1)/2, so it is the unique
representative in (2). This proves C=C* without assuming C's typing.
The routing quotient is then

    K0=1+(E mod R0)>0.

In particular, a=0 is permitted with K0=1, and a=t-1 represents
the identity tail rotation with K0=E+1. No nonzero-prefix assumption
on E is needed.

The derived A=C+Q has no carry: it appends a top digit 1 to the
length-(t-1) Boolean word C. If D's digits are d=(1,d1,...,d_(t-1)),
then A has digit word

    P_a(d)=rotate_right_a(d1,...,d_(t-1)) followed by (1).   (3)

Before typing B, positivity and A+B=S<=2H imply 0<B<q-1.
The second factorization forces R1=3^b for 0<=b<=t. As in the
reviewed 66-operation component, the unique residue modulo q-1 shows
that B is the full cyclic right rotation Q_b(d). Positivity of K1
excludes b=0; b=t represents the identity. For every 1<=b<=t,

    K1=D mod R1>0

because D's units digit is 1. Hence both ports are Boolean before the
NAND identity is inferred from A+B=S.

Precisely, (1) has positive witnesses if and only if the selector
predicate holds, D has at least two one digits, R0=3^a with
0<=a<=t-1, R1=3^b with 1<=b<=t, and

    d=NAND(P_a(d),Q_b(d)),
    the digitwise input-count word equals S.               (4)

The last condition retains the selector's exact labels, including both
input units digits being zero. It cannot be omitted or silently replaced
by an unrestricted Boolean fixed-point claim.

## 3. Positive converse

Given data satisfying the exact semantics (4), take Q=q/3,
E=(D-1)/3, C=rotate_right_a(E), J=Q-C, and B=rotate_right_b(D).
Then E,C,J,B,Q are positive. Set

    Z0=Q/R0, K0=1+(E mod R0),
    Z1=q/R1, K1=D mod R1.

These are positive integers and satisfy every equation in (1).
The reviewed selector theorem provides its positive Pell witnesses.
Thus the stated finite relation has both directions, including the
strictly positive supplied domain.

## 4. Paid ledger

Append these 19 instructions to the complete 54 schedule:

    D=twice_H-F2; S1=H+F2; S=S1-F0;
    A=C+Q; ports=A+B;
    E3=3*E; Eword=E3+1; q_from_Q=3*Q;
    tail_modulus=Q-1;
    RA0=R0*C; lhs0=RA0+tail_modulus;
    guard0=tail_modulus*K0; rhs0=E+guard0;
    div0=R0*Z0; boundQ=C+J;
    RA1=R1*B; guard1=twice_H*K1; rhs1=D+guard1; div1=R1*Z1.

Compare Eword=D, q=q_from_Q, Q=div0, boundQ=Q, lhs0=rhs0,
ports=S, RA1=rhs1, and q=div1. The additions are 8M+11A, giving
73=37M+36A. This is seven operations above the 66 NAND relation.
The literal checker expands all 21 comparisons against independent
polynomials, retaining the selector's previously reviewed auxiliary-norm
correction.

## 5. An admitted noncommuting example

Take

    q=243, H=121, F0=122, F1=229, F2=133,
    Q=81, E=36, C=12, J=69,
    R0=3, Z0=27, K0=1;  R1=9, Z1=27, K1=1.

Then D=109, A=93, B=39, S=132. Their ternary digits, from low to
high, are

    d=(1,0,0,1,1), P_1(d)=(0,1,1,0,1), Q_2(d)=(0,1,1,1,0).

The selected labels are (0,2,2,1,1), so both ports have the required
initial zero and their NAND is d. Extending (3) to arbitrary words by
moving their actual initial digit, the two position permutations give

    P_1 Q_2(d)=(1,1,0,1,0),
    Q_2 P_1(d)=(1,0,1,0,1).

They do not commute, and d is not invariant under their composition.
Consequently the homogeneous commuting-permutation NAND collapse does
not apply to this admitted instance.

A tail rotation that instead leaves the initial digit in place would
force A's units digit to be 1. Such a composition would contradict the
fixed initial selector. Moving that bit to the top in (3) is essential.

## 6. The extra bound is necessary

Dropping C+J=Q saves one instruction but destroys typing. An explicit
case satisfying every remaining comparison is

    q=243, Q=81, H=121, (F0,F1,F2)=(122,133,229),
    D=13, S=228, E=4, C=108, A=189, B=39,
    R0=3, Z0=27, K0=5; R1=81, Z1=3, K1=13.

Here C>=Q, and A has ternary digits outside {0,1}. Its selectors are
valid, with labels (0,1,1,2,2), so the full positive selector theorem
supplies the inherited kernel witnesses. The weakened 72-operation
relation therefore has an actual soundness counterexample to the desired
Boolean routing semantics. The bound is not merely a convenience of the
proof.

## 7. A finite-defect restriction

Let P,Q,R be permutations of a finite coordinate set, with Q and R
commuting. Suppose P and R disagree on at most m coordinates. For a
Boolean vector d satisfying d=NAND(Pd,Qd), put T=RQd. Then

    Hamming(d,T)<=2m.                                      (5)

Here permutations act by rearranging vector coordinates, and Hamming
counts coordinates with unequal entries. Substituting the NAND relation
into its two input vectors gives the Boolean identity

    d=(P^2d AND PQd) OR (QPd AND Q^2d)
      <= PQd OR QPd.

The words PQd and QPd each differ from T at at most m positions:
for the first, compare P with R on Qd; for the second, apply Q to
Pd and Rd and use QR=RQ. Each word also has the same number of
ones as T. Consequently each has at most m/2 one entries at positions
where T is zero. Their union has at most m such positions, and the
displayed inequality gives at most m one entries of d outside T.
Since d and T have equal numbers of ones, their Hamming distance is
twice that number. This proves (5).

For the family (3), if a=0 or a=t-1 then P_a is exactly the full
right rotation R_1, so m=0 recovers rotation invariance. Otherwise
1<=a<=t-2. The explicit coordinate map is

    (P_a d)_j=d_(1+((j+a) mod (t-1)))  for 0<=j<t-1,
    (P_a d)_(t-1)=d_0.

It agrees with R_(a+1) except on the final a+1 positions, and agrees
with R_(a+2) except on the first t-a-1 positions and the final position.
Thus one can choose s=a+1 with m=a+1, or s=a+2 with m=t-a, and
(5) yields

    Hamming(d,R_(s+b)d)<=2m.

In particular one may choose m=min(a+1,t-a), with its corresponding
s. This is a restriction when the defect region is small. When a and
t vary, m need not be bounded, so this lemma is not a uniform
finite-state reduction or a nonuniversality theorem. Even for bounded
m, arbitrary circuit wiring does not follow from the existence of the
noncommuting permutations. The lemma has independent mathematical
checks from both the composition and Pell review lanes; no extra
computational evidence is claimed for it.

## 8. Evidence and remaining scope

The author audit and two independent full scoped proof/source/receipt
reviews pass. The root default replay matched the saved receipt. These
checks concern this finite relation, not a universal certificate.

The checker proves symbolic source identities and the paid count,
enumerates arbitrary positive bounded ports for all selector words
through t=6, and verifies the concrete noncommuting instance and the
missing-bound counterexample. Its default invocation compares the saved
receipt; `--write` recreates it. Neither frozen selector nor frozen 66/67
package is edited. The complete 73 source, positive-domain proof and
saved-receipt replay passed independent review in both the root and Pell
review lanes. Section 7 adds mathematical analysis without changing the
literal source or its receipt.

The arithmetic theorem does not show that this special permutation family
can encode arbitrary circuit incidence. The maps are rotations followed
by a permutation of one interval, with existential lengths and offsets.
Their possible structural restrictions need separate investigation. A
noncommuting pair alone does not establish universality, and no input or
acceptance construction is included in the 73 count.
