# Shifting the fixed program offset gives258 operations

The later [positive-history-scale compiler](neary_woods_universal_history_scale257.md)
gives257 operations and degree at most1384, with a positive-zero slack
bijection on valid program/input slices. Its [new partition search](neary_woods_universal_history_scale_partitions.md)
reaches269/212 with44 witnesses and265/456 with43. The separate
[shifted-offset partition search](neary_woods_universal_offset_partitions.md)
retains this packet's older scale and its historical degree bounds.

The [literal builder](neary_woods_universal_offset258.py) saves one addition
from the [259-operation lower-unit compiler](neary_woods_universal_lower_unit259.md).
Its default has **258=133M+125A**,257 certificate operations, one comparison,
43 positive witnesses and degree **at most3861**. Four positive program
parameters and the ordinary positive input remain; the separate fifth
fixed duration-bound interface is also supported. The [receipt](neary_woods_universal_offset258.json)
stores the selected complete sources and counts.

The fixed program offset now represents E-1 instead of E. The other three
program parameters and the fixed U9 numerals have their previous meanings.
The accepted ordinary inputs are identical on the corresponding valid
program slices. This is not a bijection of all supplied positive tuples:
the exact affine map to the parent can turn either private gap into zero
or a negative integer away from its positive domain. The proof treats
soundness and positive completeness separately. The established75/87
bounds are unchanged.

## 1. The fixed sentinel offset remains a sufficient positive bound

In the [actual U9 input construction](neary_woods_universal_u9_tag_chain.md),
Section2, the old E is the sentinel integer of the concatenated fixed
PREFIX, MIDDLE and TAIL binary strings. Let their total encoded length be L.
Those fixed strings encode all b_S fixed binary tape cells by nonempty
blocks, and b_S>0. Thus L>=b_S>=1. A sentinel of length L satisfies

    E>=2^L, E'=E-1>=2^L-1>=L>=b_S>=1.             (1)

The elementary inequality holds already at the minimal length L=1,
with equality2^1-1=1. No large-program assumption or materialization
of E is needed. Every valid old program recipe therefore yields a
strictly positive new parameter E'.

With the default merged bound the source still emits

    n=program_E+program_duration_gap=E'+positive_gap.

The native recoder restores the same dyadic duration n as before. By(1),
n>b_S, and the actual binary tape length still satisfies

    64n<64n+b_S<128n.                              (2)

Hence the least permitted dyadic counter is exactly128n. The physical
head cut, order, counter and ordinary-input padding conditions are unchanged.
With the separate fifth parameter, its inherited valid bound remains fixed
and positive and continues to pay the same length condition; only E shifts.
Arbitrary small E' values not produced by a valid recipe receive no such
semantic guarantee.

Before typing, E'>=1 and every supplied gap is positive. All loader and
recoder expressions needed for the260/259 pretyping argument therefore
remain positive on their original unconditional domains. In particular
the new duration is at least2, q exceeds x plus that duration, and the
paid loader Q=κ*(q+z+power_gap)+1 still supplies its original positive
scale and modular conditions. No typed relation is being assumed to
justify these inequalities.

## 2. One literal gate disappears

Write W for the value actually emitted as `load__tag_input` by the new
source. The old loader formula has the form

    V0=((program_A*r+program_B*z)*Q+program_T*r)+E.

The new program recipe supplies E'=E-1, so

    W=V0-1.                                       (3)

All other loader rows are unchanged. The259 parent computed the lower
factor as1+R_V-L_V, where L_V=b*N_V+loaded_value. The new source computes

    N_L=R_V-L_V=H_V+P*V_f-b*N_V-W.                 (4)

It replaces the two private difference/plus-one rows by one subtraction.
Their sole consumer is the unit group; all other old rows remain. This
removes exactly one addition from the certificate and final polynomial.
The factor partition, comparison list, witnesses and other unit factors
are unchanged. The zero-ordinary-residual finalizer remains the product
minus1, as in259. Active metadata identifies the true initial value as
`load__tag_input+1`; there is no emitted register for that value and no
unpaid arithmetic gate. The old259 packet is retained only as provenance.

The emitted height is now

    D=U_f+W+V_f+height_gap.

All four terms are positive before equations. In particular
D>=W+3>W+1=V0 on a valid slice. Thus the reduced height contribution still
strictly bounds the true initial value; it also bounds V0-2. This margin
is needed in the signed lower-history argument.

## 3. Soundness on the new program slices

At a new positive zero the integer group factors are units. The proof of259
through native typing, both index signs, the mask sign, all selected history
products and the upper transport applies without change. It does not use
that the emitted lower input is the true sentinel. It uses its positivity,
the weakened signed global bound, and the unchanged paid scale/duration
relations, all retained here. The signs of N_L and the global history
factor N_G remain temporarily free.

Equation(4) gives the carry-free lower history with initial value

    W+N_L = V0              if N_L=+1,
    W+N_L = V0-2            if N_L=-1.              (5)

Both candidates are positive and strictly below D. The valid loader
recipe and the restored recoder show that V0 is the sentinel of E(w) for
the actual initialized tag word w ending in b. That statement applies
to W+1, not W itself. All program coefficients retain their inherited
fixed meanings except the explicit one-unit shift in E.

The negative sign is impossible by the259 forbidden-word lemma: V0 has
binary form P0 1 0^beta, with P0 odd and beta>=2. Subtracting2 gives
P0 0 1^(beta-1)0, containing an internal101. No lower append can remove
it, whereas upper tiles and the final10^beta have only zero runs of
length beta. Thus N_L=1. The remaining global factor is then1 as well.
The decoded history has exactly the genuine initial sentinel V0 and the
original terminal relation. The complete tag/clockwise/U9 theorem therefore
gives acceptance of the original ordinary input, with the exact counter
in(2). This establishes soundness without lifting a possibly zero private
gap to a supplied positive parent coordinate.

## 4. Positive completeness and an exact affine source identity

For a new assignment, define the algebraic parent assignment by

    E_old=E_new+1,
    height_gap_old=height_gap_new-1,
    duration_gap_old=duration_gap_new-1       (merged bound only).
                                                        (6)

With the separate bound, leave duration_gap unchanged. This keeps the
computed duration, both native scales and the history height D identical.
The old loaded input and its two intermediate height sums increase by1;
the old lower left side also increases by1. The old difference row is
one less than the new lower unit. Its subsequent plus-one restores exactly
that new unit. Every other retained source register, every group product,
every comparison and the complete polynomial agree exactly under(6).

These are affine polynomial identities over all integers, including signed
ones. Map(6) is not asserted to preserve the positive domain: for example
a new height gap of1 maps to zero. Source tests deliberately permit these
boundary values. Soundness instead follows from Section3.

For positive completeness, start with any positive259 zero on an old
valid program slice and take the inverse affine map:

    E_new=E_old-1,
    height_gap_new=height_gap_old+1,
    duration_gap_new=duration_gap_old+1       (merged bound only).
                                                        (7)

Equation(1) proves the new program parameter positive. All new supplied
witnesses are positive; all unchanged witnesses remain positive. Identity(6)
therefore proves a new zero at the same ordinary input. The original U9
proof supplies every accepting input with such a parent zero, using its
already paid synchronized padding. This proves complete accepted-input
equivalence under the fixed recipe change. No new input recoding, unchecked
program-length oracle or additional existential coordinate is introduced.

## 5. Literal counts, guards and checks

The certificate costs257=133M+124A with one comparison and43 witnesses;
its final subtraction gives258=133M+125A. Every considered schedule saves
one addition from its corresponding259 wrapper. The complete propagated
degree dictionaries are unchanged, including the guarded exact main-norm
cancellation. The default bound is3861. The selected mapped269/608 option
has44 witnesses; a266/1344 option retains43 witnesses. These are mapped
schedules, not a new exhaustive optimization over partitions.

The guard rebuilds the exact259 caller and checks all source rows, domains,
fixed-numeral roles, nested active interfaces, factor groups and counts.
It additionally checks the complete consumers of E, both shifted gaps and
the erased private difference; the difference has no other consumer or
active export. Every new source gate must reach the final output.

```sh
python3 neary_woods_universal_offset258.py
```

The receipt audits76 source/degree/count ledgers:32 canonical base/interface
choices and44 distinct mapped schedules. It checks1,216 full source/output
identities, including304 signed arbitrary assignments and608 positive
parent-to-new projections. The tests use independent sampled fixed roles
for algebra; they do not assert valid programs or full Pell zeros. Five
incompatible callers exercise consumer/export/source guards. An additional
512 fixed-sentinel cases cover encoded lengths1 through128 and verify the
positive E-1 bound and exact counter inequalities.

Author receipt generation and a separate fresh default replay pass. Root
independently reviewed the complete proof, source, active metadata and the
actual U9 input/frame, duration282 and loader288 dependencies, then ran a
fresh default replay: all pass with no findings. A separate root executor
and manual affine map checked256 complete outputs (128 signed) across all32
canonical base/interface choices,32 height-gap1 to old-gap0 boundary cases,
and48 additional sentinel bounds at lengths129,257,511 and1024. These
algebra and bound fixtures make no full-positive-inverse or Pell-zero claim.
Franklin independently reviewed the full proof and source and ran a fresh
default replay, all with no findings. His own executor and manual affine
maps passed576 complete output, retained-register and residual identities
(144 signed) across36 contexts, covering all16 bases and both interfaces
plus lower-degree schedules;36 zero-height and18 zero-duration lifts also
passed. He checked125 additional sentinel/height cases and24 encoded-length
cases through length2047; all four local links resolve. The trio is frozen
after these reviews. No frozen parent source, shared navigation or Git state
is modified by this packet.
