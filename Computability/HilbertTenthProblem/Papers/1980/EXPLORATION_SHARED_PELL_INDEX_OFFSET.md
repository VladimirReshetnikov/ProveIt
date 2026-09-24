# Reusing the Pell index for the global offset: 109 operations

The existing Pell register tr1=2r+1 can impose the global native offset
without a supplied wide repunit. In the complete110 construction replace

    2Jwide+1=D0, r=Praw+Jwide

by the single equation

    tr1=D0+(Praw+Praw).                         (1)

Here Praw is the unchanged twelve-field raw Horner word and D0=q^12
is the unchanged computed scale. The register tr1 is already evaluated
as (r+1)+r for the retained main Pell index. The packed bound
r+beta=D0, all positive raw fields, and the fixed compiled program are
unchanged.

The result is **109 operations:55 multiplications and54 additions or
subtractions**, with **38 positive unknowns and26 equations**. The
complete source/checker is `../verification/explore_shared_pell_index_offset.py/.json`.
The frozen predecessor is `EXPLORATION_GLOBAL_NATIVE_OFFSET.md`, with
its positivity/compiler lemma `EXPLORATION_GLOBAL_OFFSET_POSITIVITY.md`.
The established universal frontier remains90.

## 1. Exact source identity and positive witness correspondence

Let the old packing and wide-geometry residuals be

    F=r-Praw-Jwide,
    G=2Jwide+1-D0.

The new residual is exactly

    N=2r+1-D0-2Praw=2F+G.                       (2)

Thus every110 solution yields a109 solution by deleting only Jwide.
Every retained positive coordinate, raw packed word, scale and Pell
witness keeps precisely its previous value. This direction requires
no digit interpretation or divisibility argument.

Conversely, the retained source q=2J+1 and positive J imply that q>=3
is odd before any power recovery. Therefore

    Jwide=(q^12-1)/2

is a uniquely determined positive integer. Define this coordinate from
any109 solution. Its old geometry residual G is zero. Equation(1)
then gives 2F=N=0, so F=0 over the integers. Every other old source
is literally unchanged and contains no Jwide. This restores a110
solution with every other coordinate fixed.

The two maps are inverse because the old wide geometry uniquely fixes
Jwide. They are an exact positive-witness bijection, valid before the
kernel, Boolean decoding, finite-program interpretation or parity proof.
No new runtime division is being counted: division by2 occurs solely
in the mathematical existence proof for an eliminated coordinate.

## 2. Bounds, compiler and positive converse

The previous full proof applies through this exact bijection. In
particular the unchanged bound r+beta=q^12 still implies

    Praw<=(q^12-1)/2.

The top raw field therefore bounds the intrinsic program width. The
positive raw sign and zero pairs give the same bounds for T and the
two numerical tracks, and the unchanged kernel and raw packing decode
the same finite path. No stronger lower or upper bound is assumed.

The fixed prefix still contains the harmless mandatory zero request
on its initially zero second register. It ensures the strictly positive
raw zero word; the unit-walk argument ensures both raw numerical tracks
are positive. The other positive raw fields and the cyclic first-return
interpretation are unaltered. The marked compiler, its fixed numerals
and the intrinsic forbidden-position mask require no recompilation for
this reduction.

For every positive input in the represented recursively enumerable set,
construct the complete110 witnesses and discard Jwide. This preserves
the exact even packed index and every positive fixed-sign Pell witness.
For the opposite implication, restore the unique positive Jwide first
and use the110 soundness theorem. The resulting109 family consequently
has precisely the same ordinary-input universal semantics.

## 3. Exact operation count

Delete exactly these three evaluated additions:

    twice_Jwide=Jwide+Jwide,
    wide_geometry=twice_Jwide+1,
    packed=raw_packed+Jwide.

Add exactly two evaluated additions:

    twice_raw_packed=raw_packed+raw_packed,
    packed_index_rhs=D0+twice_raw_packed.

Compare packed_index_rhs with the already needed tr1. The raw Horner
word, power chain, source bound and all Pell instructions are unchanged.
Hence110-3+2=109, with55 products and54 additions/subtractions. One
supplied positive coordinate and one comparison disappear, leaving38
unknowns and26 comparisons. Equality tests and fixed numerals have the
same cost convention as the predecessor.

The checker expands every new source against the actual acyclic
register schedule. Equation(2) is checked symbolically, as are the
inverse substitution and the inherited auxiliary-norm correction.
The new two additions may be evaluated immediately after D0: the
comparison is made after the full schedule, when tr1 has been computed.
There is no forward dependency in an arithmetic instruction.

## 4. Evidence boundary

The finite integer regression includes ordinary odd radices that are
not powers of three, deliberately overflowing raw fields, and rejected
nonpositive packed slacks. It checks exact index transport and rejects
perturbed indices. These are algebra checks, not claimed controller
solutions.

The complete canonical raw words, source witnesses and central
valuations from110 do not change under the forward map. Their receipt
is explicitly labelled inherited; it is not presented as a fresh
evaluation of unchanged enormous values. The new polynomial source
identity transports all17 old outer comparisons to the16 new ones.
The general positive-witness theorem, rather than any finite sample,
establishes the reduction for all represented inputs.
