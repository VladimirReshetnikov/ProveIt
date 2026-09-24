# Factoring the four raw program fields: 108 operations

The high four fields of the109-operation raw construction can be
evaluated together, without separately supplied test words TC and TV.
Replace their definitions and their six-operation Horner block by

    Bprog=(1+q^2)(C+qV)+q^2[J+(q Zstar-S)H].       (1)

The low eight positive raw fields are unchanged and are appended below
this block by the same Horner operations. The retained scale is D0=q^12,
the retained global-offset equation is tr1=D0+2Praw, and the retained
packed bound is r+beta=D0. All fixed program numerals remain unchanged.

This gives **108 operations:55 multiplications and53 additions or
subtractions**, with **36 positive unknowns and24 equations**. The source
is `../verification/explore_factored_raw_program_block.py/.json`.
Its frozen predecessor is `EXPLORATION_SHARED_PELL_INDEX_OFFSET.md`.
This remains an alternative universal family above the existing90 bound.

The only potentially problematic elimination is the strict positivity
of TC. It is recovered below from the packed bound before any digit or
kernel argument. No untyped test word is assumed positive.

## 1. The exact four-field identity

Define the mathematical expressions

    TC*=C+J-SH, TV*=V+Zstar H.                    (2)

They are not yet supplied coordinates. Direct expansion gives

    Bprog=C+qV+q^2 TC*+q^3 TV*.                   (3)

The coefficient q Zstar-S is positive: q>=3 from q=2J+1, and the
fixed intrinsic-width construction gives Zstar>3S>0. Thus the evaluated
formula(1) is positive even before TC* is known positive.

Let Low8 denote the raw polynomial in the eight unchanged lower fields.
Every one of those fields is still supplied positive. Consequently

    Low8>0, Praw=Low8+q^8 Bprog>0.

The old support and test-V residuals were

    FC=C+J-SH-TC, FV=TV-V-Zstar H.

Writing Nold and Nnew for the old and new doubled-index packing
residuals, their exact relation is

    Nnew=Nold-2q^10 FC+2q^11 FV.                 (4)

The checker verifies both(3) and(4) by polynomial expansion.

## 2. Recover strict positivity before typing

The unchanged two geometries and the doubled-index equation imply

    r=Praw+(q^12-1)/2.

The unchanged positive packed slack therefore implies

    0<Praw<=(q^12-1)/2.                          (5)

Put Q=V+(Zstar-S)H. This is a positive integer, because V,H>0 and
Zstar>S. Expansion of(3) gives the strict lower bound

    Praw>Q q^11.                                (6)

Here is the complete positive difference, which remains valid if TC*
were negative:

    Praw-Qq^11
      =Low8+Cq^8+Vq^9+(C+J)q^10
         +SH(q^11-q^10)>0.                      (7)

Since q is odd and at least3,

    floor[(q^12-1)/(2q^11)]=J.

Equations(5),(6) give Q<=J. In particular

    J>(Zstar-S)H,
    R-1=2J/H>2(Zstar-S)>2S.                     (8)

The equality in(8) is merely reasoning from the retained source
H(R-1)=2J. No division is an uncharged arithmetic instruction. The last
inequality uses the fixed Zstar>3S, which is stronger than necessary.
It follows immediately that

    TC*=C+J-SH>0, TV*=V+Zstar H>0.               (9)

Thus both eliminated test coordinates can be restored as strictly
positive integers. This step precedes Booleanity of every field,
ternary power recovery, support decoding and the Pell kernel.

After(9), all twelve mathematical fields in(3) and Low8 are positive.
The ordinary top-field argument then gives TV*<=J and the stronger
intrinsic width R-1>2Zstar. Hence none of the predecessor's program
width conditions is weakened by the elimination.

## 3. Exact positive-witness equivalence and universality

From a109 solution, discard TC and TV. Equation(3) shows that the
computed Praw is numerically unchanged. Equation(4) gives the new
packing source, and all other retained sources are identical. Every
remaining positive coordinate is unchanged.

Conversely, from a108 solution define TC and TV by(2). Section2 proves
that these are positive before using any predecessor theorem. Their
two defining source residuals vanish identically. Equation(3) restores
the old raw packing, and(4) then restores its packing equation. Thus
all109 source equations hold. The coordinates in(2) are uniquely
determined, so these maps are inverse positive-witness maps.

In particular the full marked-prefix compiler, cyclic first-return
interpretation, ordinary raw input, positive raw tracks, both zero
labels, packed index parity and every positive Pell witness are
unchanged. No fixed program numeral needs adjustment. For any
recursively enumerable set, use the same fixed109 program and discard
the two coordinates. The resulting108 system accepts exactly that set.
The converse restores those coordinates before applying109 soundness.

## 4. Ten operations replace eleven

The former support definition costs three operations:

    SH, C+J, SH+TC.

The former test-V definition costs two:

    Zstar H, V+Zstar H.

Their four-field raw Horner block costs another six. Those eleven
operations contain five products and six additions/subtractions.
The replacement evaluates(1) in exactly ten operations:

    qV, C+qV,
    1+q^2, (1+q^2)(C+qV),
    q Zstar, q Zstar-S,
    (q Zstar-S)H, J+(q Zstar-S)H,
    q^2[J+(q Zstar-S)H], their final sum.

These contain five products and five additions/subtractions. The
existing q^2 multiplication is moved before this block and remains
counted exactly once; it still feeds the retained scale power chain.
The eight lower-field Horner steps, the global doubled-index link,
the positive packed bound and all kernel operations are untouched.
The complete count is therefore109-1=108, with36 unknowns and24
comparisons after deleting the two supplied test coordinates.

The register `q2_plus_one` is named explicitly for possible later
sharing. This certificate makes no claim for an additional reduction
from a separate change to the lower fields.

## 5. Verification scope

The checker verifies every primitive source comparison, the full
four-field identity, the elimination combination(4), and the unchanged
acyclic norm correction. Its finite positivity regression deliberately
includes formal TC* values that are zero or negative; all such cases
fail the retained packed bound. It also covers ordinary integer widths
that are not powers of three, so the tested implication does not
silently presuppose power recovery. Its lower fields are explicitly
positive placeholders, not claimed complete controller witnesses.

The complete canonical packed words and central valuations inherited
from109 remain numerically unchanged. Their receipt is labelled
inherited evidence; the new polynomial identity transports all16 old
outer comparisons to14. Full positive-witness equivalence is supplied
by the general proof, rather than by a finite rerun of unchanged large
Pell coordinates.
