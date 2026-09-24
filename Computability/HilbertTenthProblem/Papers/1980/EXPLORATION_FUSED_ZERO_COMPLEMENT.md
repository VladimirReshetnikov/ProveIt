# Fusing the zero word with its complement: 108 operations

In the complete 109 construction, the adjacent raw words Z and D satisfy
Z+D=H. Their packing contribution is therefore

    Z+q D = H+(q-1)D = H+(2J)D.                 (1)

The register twice_J=2J is already required by the geometry and routing.
Using (1) in the packing removes the positive variable Z and its sum
comparison, saving one addition. The count is **108 operations, 55
multiplications and 53 additions/subtractions**, with **37 positive
unknowns and 25 equations**. All twelve semantic mask words remain.
The existing universal frontier remains 90. Full independent proof/source
review and fresh verification pass.

The source and receipt are `../verification/explore_fused_zero_complement.py/.json`.
The predecessor is `EXPLORATION_SHARED_PELL_INDEX_OFFSET.md` and the
raw-positivity/compiler lemma is `EXPLORATION_GLOBAL_OFFSET_POSITIVITY.md`.

## 1. Exact schedule and source identity

Let Prog=C+q V+q^2 TC+q^3 TV. The two old Horner stages are

    D+q Prog, Z+q(D+q Prog).

They cost two multiplications and two additions. Replace them by

    q^2 Prog, (2J)D, H+(2J)D, q^2 Prog+(H+(2J)D).

The cost is again two multiplications and two additions; q^2 is already
computed for q^12 and is moved before packing. Delete the addition Z+D.
All other arithmetic instructions remain unchanged. No operation has a
forward reference. The supplied variable Z and one equation disappear.

Define Z=H-D solely as a mathematical abbreviation. Off the geometry
equation, the implemented raw packing differs from the old substituted
packing by -(q-2J-1)D q^6. Consequently the exact source identity is

    new_pack = old_pack[Z:=H-D] + 2q^6 D old_q_geometry. (2)

Every other retained source is literally the old source after this
substitution. The old zero-pair residual becomes identically zero.
The checker verifies (2), all 25 complete source comparisons, and the
unchanged auxiliary norm correction against the actual 108 instructions.

Every old positive solution immediately gives a new positive solution
with the same retained coordinates and packed integer. For the inverse,
positivity of Z must be proved: H-D is not automatically positive from
the remaining supplied-variable declarations. The proof follows.

## 2. Width and bounds before decoding

Use the retained q=2J+1 and the shared-index packing equation to define
the proof-only positive integer Jwide=(q^12-1)/2. Then r=Praw+Jwide.
The bound r+beta=q^12 implies 0<Praw<=Jwide.

This positivity does not assume Z>=0. Group its two positions by (1):
H+(q-1)D>0 because H,D>0 and q>=3. The other ten raw fields are
supplied positive. In particular Praw>q^11 and its top field obeys
TV<=J. As TV=V+Zstar H, V>0 gives R-1>2Zstar. The unchanged intrinsic
forbidden-position digit therefore enforces R>=9, H<=J/4, q>=R^3,
and all fixed program-width inequalities before applying the kernel.

The retained sign pair yields 0<Kp,Km<H. Write A=A0+A1 and
delta=Kp-Km. The time equation gives A<WH/(W-1)<J as before.
Since D>0 and R>3, the top equation 6(J-T)=(R-3)D gives 0<T<J.
Thus A0,A1<J and B0,B1=A0,A1+T<2J<q.

T>0 also gives the two useful strict bounds

    D < 6J/(R-3) <= J,
    D < 3(R-1)H/(R-3) <= 4H.                  (3)

The second uses R>=9. Hence Z=H-D>-J. It may still be negative.
For routing, the unchanged fixed mask satisfies Zstar>hs+4hz, since
its fresh digit was chosen above 6(hs+hz). Therefore

    0<O=V+hs Kp+hz D<V+Zstar H=TV<=J<q.

The original route estimate gives C<q before its Booleanity is assumed.
Also V<TV<=J and TC=C+J-SH<q+J. The grouped positive packing gives
r>q^11 and r<q^12, so all 43-operation kernel bounds hold: D0=q^12>=81,
r>=27, r<2D0 and D0<r^2. No unproved sign condition on Z was used.

## 3. The Boolean mask excludes a negative Z

The kernel recovers q as a power of three and forces r's twelve-block
ternary representation to have only digits one or two. Subtracting
Jwide digit by digit gives a Boolean raw Praw, with unit digit one.

The first six raw words Kp,B0,A0,B1,A1,Km are positive and below q.
They therefore decode without carries. At the next two positions lies

    X=H+(q-1)D=Z+qD.

From 0<D<J and H<=J/4, one has 0<X<q^2, so this pair has no outgoing
carry. If Z<0, then -J<Z<0 and its two actual base-q chunks are

    q+Z, D-1.

The lower chunk satisfies q+Z>q-J=J+1. This is impossible for a Boolean
ternary word of length log_3(q), whose largest possible value is J.
Thus Z>=0. Both Z and D are now the actual chunks, are Boolean and
below q, and satisfy Z+D=H. The possibility Z=0 is retained at this
stage; the local mask alone does not exclude it.

The subsequent C and V chunks decode because their previously proved
bounds are below q. Once C is typed, C<=J, so TC=C+J-SH<2J<q.
TV<=J was already established. All twelve semantic raw mask words are
therefore correctly typed, with no unchecked carry at either boundary.

## 4. The compulsory zero request restores strict positivity

For completeness, one can restore the full 114-operation intrinsic-width
system at this point: supply J plus each of the twelve raw fields as
its native fields. Even the possibly zero Z gives the strictly positive
native value J+Z. All retained raw program coordinates are positive.
The substituted old packing is the same r by (2), and every old source
holds. Thus the complete intrinsic-width soundness theorem applies with
the same fixed annotated compiler and recovers its finite accepting path.

The first positive return must traverse the forced initial prefix. Its
second lane has the compulsory true zero request on the initially zero
second register. Its corresponding coefficient in Z is one. Hence Z>0.
For the canonical six-state table, the only outgoing edge from state zero
goes to state one, whose zero label is one; the checker verifies that
specific fixed-table fact as well. For arbitrary represented sets, the
marked-prefix compiler lemma provides it before compiling fixed numerals.

Restoring this positive Z yields a full 109 solution, with every other
coordinate unchanged. The old pair equation makes this extension unique.
The forward and inverse maps are therefore an exact positive-witness
bijection for the fixed annotated universal family. The reverse proof
uses the existing complete history theorem, rather than assuming the
eliminated raw variable is positive before decoding.

The positive converse simply constructs the predecessor's witnesses and
deletes Z. The packed index, its parity, all other supplied positive
coordinates and every fixed-sign Pell witness retain precisely their
values. No new ordinary-input encoding, program graph or numeral is used.

## 5. Evidence boundary

The checker freshly expands all source comparisons and tests the exact
pair and borrow inequalities over ordinary odd radices, including
nonpowers. Boolean conclusions are tested only when the radix is a power
of three. Cases with Z=0 are deliberately allowed by the local regression;
the separate decoded-prefix proof establishes its strict positivity.

The full canonical examples and valuations are unchanged from 110/109.
Their receipt is explicitly inherited. The freshly checked source identity
transports all sixteen old outer comparisons to the fifteen new ones.
Enormous Pell coordinates are supplied by the unchanged positive converse.
