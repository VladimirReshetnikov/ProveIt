# Affine paired-SL2 input cannot give universal subgroup membership

An entrywise affine integer curve in SL2(Z) cannot encode a general
computably enumerable set by membership in a fixed subgroup. The same
obstruction holds for a block diagonal target with **two independently
chosen affine SL2 blocks**. Its integer membership set is empty or a
coset of a subgroup of Z. On positive inputs, this gives only an empty
set, a singleton, or one full residue class; all positive integers are
the period-one case.

Consequently, the quadratic degree in the
[group substrate's ordinary-input matrix curve](group_commutator_universal_substrate.md)
is necessary **within this particular interface**. This is not a lower
bound on arithmetic operations, witness counts, or arbitrary Diophantine
representations. The argument is elementary and self-contained.

## 1. Every affine SL2 curve is a translated power curve

Let C,D be integer 2-by-2 matrices and suppose

    L(x)=C+xD,                 det L(x)=1 identically.             (1)

It is enough to require determinant one for every positive integer x:
the determinant is a polynomial of degree at most two, so equality on
that infinite set implies the polynomial identity. In particular det C=1,
even when zero is outside the intended input domain.

The inverse of C has integer entries. Set N=C^-1 D. Then

    L(x)=C(I+xN),
    det(I+xN)=1+x trace(N)+x^2 det(N)=1.

Comparing coefficients gives trace(N)=det(N)=0. The two-dimensional
Cayley--Hamilton identity now gives N^2=0. Put P=I+N. The exact identity

    (I+sN)(I+tN)=I+(s+t)N

holds for all integers s,t, and (I+N)^-1=I-N. Therefore

    P^x=I+xN,                 L(x)=C P^x                        (2)

for every integer x, including negative x. Both C and P belong to SL2(Z).
No assumption that C commutes with P has been made or is needed.

The constant case D=0 gives N=0 and P=I. If N is nonzero, P has infinite
order over the integers, since P^x=I implies xN=0.

## 2. Subgroup membership on a translated cyclic sequence

The following fact holds in any group. Fix elements C,P and a subgroup K,
and let

    T={x in Z : C P^x belongs to K}.

If T is empty there is nothing to classify. Otherwise choose x0 in T.
For any integer x, the **left quotient** is

    (C P^x0)^-1 (C P^x)=P^(x-x0).                                (3)

Thus C P^x belongs to K only if P^(x-x0) belongs to K. Conversely, if
P^(x-x0) belongs to K, multiplication after the known element C P^x0 in K
gives C P^x in K. Hence

    T=x0+H,        H={n in Z : P^n belongs to K}.                  (4)

The map n -> P^n is a group homomorphism, so H is a subgroup of Z.
Every such subgroup is dZ for a unique nonnegative integer d, with
0Z={0}. Therefore T is one of

* the empty set;
* a singleton, when d=0;
* a full residue class x0+dZ, when d>=1.

In particular, the last case contains **every** integer in that residue
class, in both directions. There is no finite exceptional prefix. Upon
restricting to positive x, a singleton outside the positive domain
disappears, and a residue class becomes its usual infinite positive
arithmetic progression. Period one gives all positive integers.

Formula (3) is the step that fixes the coset direction. Moving C past P
would be incorrect in general. The theorem is a classification for each
fixed K; it does not give a uniform procedure to recover x0,d, or even to
decide whether T is empty from an arbitrary generating list for K.

## 3. Two independent affine blocks

Let L_i(x)=C_i+xD_i belong to SL2(Z) identically, for i=1,2. Apply
Section 1 separately to obtain L_i(x)=C_i P_i^x. Define

    C=diag(C_1,C_2),           P=diag(P_1,P_2).

Then

    diag(L_1(x),L_2(x))=C P^x.                                  (5)

For **any fixed subgroup K of SL4(Z)**, Section 2 applies to (5). The
subgroup need not consist entirely of block diagonal matrices. In the
specific case K lies in the block diagonal copy of SL2(Z) x SL2(Z), the
same proof may be read directly in that direct product. The repeated
target diag(L(x),L(x)) is a special case, not an additional assumption.

All resulting positive-input languages are decidable and have the
restricted shapes above. In particular, no noncomputable computably
enumerable positive set can be represented this way. Even the finite
set {1,2} is excluded. A polynomial input curve of degree zero or one
therefore cannot supply the universal paired-SL2 subgroup interface.
The companion construction uses degree two, so its degree is sharp for
this interface. This conclusion does not assert that its five arithmetic
operations are minimal.

## 4. Exact examples and the boundary of the theorem

Write

    U=[[1,1],[0,1]], V=[[1,0],[1,1]], J=[[0,-1],[1,0]].

These examples exhibit the possible cases without any undecidable
membership oracle:

* L(x)=I with K={I} accepts every integer.
* L(x)=J U^x with K=<U> accepts no integer: the target has lower-left
  entry one, whereas every member of K has lower-left entry zero.
* L(x)=U^(x-2) with K=<U^5> accepts exactly x=2 modulo 5.
* L(x)=J U^(x-3) with K=<J> accepts exactly x=3. Indeed <J> consists
  of I,J,-I,-J. The only upper triangular unipotent matrix among those
  four is I, so U^(x-3) belongs to <J> precisely for x=3.
* With two blocks, take L_1(x)=U^x, L_2(x)=V^(2x-3) and the coupled
  subgroup K={(U^n,V^n): n in Z}. Each block separately lies in the
  respective cyclic projection for every x. Membership in K requires
  matching exponents x=2x-3, and accepts exactly x=3.

Each displayed target is affine in x. These cases also distinguish
coupled subgroup membership from independently checking the two blocks.

The analogous assertion for arbitrary affine SL3 curves is false.
Let N=E12+E23, so N^2=E13 is nonzero and N^3=0, and put P=I+N. For
every integer n,

    P^n=I+nN+n(n-1)N^2/2.

The formula follows for all integers from the multiplication identity
for these three-term expressions and the case n=1. Now the affine curve

    L(x)=I+(x-1)N

has determinant one. Equality L(x)=P^n first forces n=x-1 by entry (1,2)
and then n(n-1)=0 by entry (1,3). Consequently

    {x in Z : L(x) belongs to <P>}={1,2}.

This is neither a singleton nor a coset of a subgroup of Z. The example
also embeds in SL4(Z) by adding a constant one-dimensional block. Thus
the restriction to separately affine SL2 blocks is essential; determinant
one and entrywise affinity of a general SL4 target alone do not suffice.

## 5. Executable audit and scope

The [checker](group_affine_input_obstruction.py) and
[receipt](group_affine_input_obstruction.json) use exact integers and the
Python standard library. Run the default receipt replay with

    python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/group_affine_input_obstruction.py

The checker enumerates C,D with all entries in [-2,2], retains those
with C in SL2(Z), tests the determinant coefficients, and verifies the derived
nilpotent and integer-power identities. It includes cases where C and P
do not commute. It also samples two independent affine blocks against
exact finite quotient subgroups modulo 2,3,4. Each finite subgroup is
enumerated to closure, so its full inverse image in the integer matrix
group is an exact membership fixture, without a word-length cutoff.

The finite quotient checks independently compare direct affine entry
evaluation with the coset classification and audit the left quotient
(3). Separate exact examples cover singletons, which congruence
subgroups do not produce here, and the SL3 scope counterexample. The
proof in Sections 1--3 establishes the unbounded theorem; the finite
tests audit its algebra and implementation.

An independent proof, source, and default-receipt review passed without
findings. It checked the noncommuting left quotient, both affine blocks,
the positive-domain classification, exact finite quotient oracles, and
the SL3 counterexample.

This packet changes no complete Diophantine bound. It excludes affine
input curves only under the stated matrix and subgroup interface. It
does not exclude nonlinear input loaders, different matrix substrates,
variable subgroup data, additional existential input relations, or
other computational models.
