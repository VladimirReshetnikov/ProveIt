# Fuse native junk support: 113 operations

The complete 114-operation intrinsic-width system can eliminate its
separately supplied raw TestV coordinate. Its native version is obtained
directly from native V using the same forbidden-position mask. This
saves one addition and gives **113 operations: 55 multiplications and
58 additions/subtractions**, with **41 positive unknowns and 29
equations**.

All twelve native mask fields remain. The packed integer, its positive
bound, its parity, and every supplied Pell coordinate stay unchanged
under an exact positive-witness bijection. This is therefore a complete
alternative universal family once the 114-operation predecessor is
applied; the established universal bound of 90 remains smaller.

The source and receipt are
`../verification/explore_native_junk_support_fusion.py/.json`.
The unchanged predecessor is
`EXPLORATION_INTRINSIC_PROGRAM_WIDTH.md`.

## 1. Three old equations and two new equations

Use the predecessor's notation J=(q-1)/2, positive raw junk V, native
junk NV, raw support-test word TV, and native support-test word NTV.
Let Zstar denote its fixed forbidden-position numeral, including the
extra high digit which enforces the width. The relevant old equations
are

    TV=V+Zstar H,
    NV=J+V,
    NTV=J+TV.                                    (1)

The raw coordinate TV occurs nowhere else in the source. In particular
the bound is now r+beta=q^12; it no longer uses a sum containing TV.
Packing uses NTV, and the cyclic routing uses V.

Delete the positive coordinate TV and replace (1) by

    NV=J+V,
    NTV=NV+Zstar H.                              (2)

Every other source equation and supplied variable is unchanged. The
source names in the checker are PV,PNV,PTV,PNTV for V,NV,TV,NTV,
respectively. Only PTV is removed. This is not omission of either the
V mask or its support-test mask.

## 2. Exact positive-witness correspondence

Given an old positive solution, substitute NV=J+V and TV=V+Zstar H
into NTV=J+TV. The new equation NTV=NV+Zstar H follows. Forget TV;
all the remaining equations still hold with exactly the same values.

Conversely, given a new positive solution, define

    TV=V+Zstar H.                                (3)

This is a positive integer before any power, bound or digit argument:
V,H are supplied positive and Zstar is a positive fixed numeral. The
retained adapter NV=J+V and the new support equation then imply

    NTV=NV+Zstar H=J+V+Zstar H=J+TV.

Thus all three old equations hold. The old value of TV is uniquely
determined by (3), and the two maps are inverse. This proves a bijection
of full positive witnesses, not just an equivalence of decoded paths.

In residual form, with the exact predecessor indexing,

    E23=TV-V-Zstar H,
    E26=NV-J-V,
    E28=NTV-J-TV,
    Enew=NTV-NV-Zstar H=E23+E28-E26.

The checker verifies this identity symbolically. On substituting (3),
E23 vanishes identically and E28=Enew+E26. No sign assumption about a
native field minus J is needed for this elimination.

## 3. Bounds, semantics, and positive Pell coordinates are preserved

The mask fields, in the same order, remain

    FKplus,G0,F0,G1,F1,FKminus,FZ,FZbar,NC,NV,NTC,NTV.

Consequently r=P, D0=q^12, the packed slack beta, and every kernel
coordinate are preserved numerically in both directions. Restore TV
by (3) before applying any predecessor proof. Its intrinsic width
argument then starts in precisely the same way:

    NTV<q, NTV=J+TV, TV=V+Zstar H>0.

These imply Zstar H<J and hence the required lower bound on R. The
kernel, low-field carry recovery, typed flags, C<q argument, native
program decoding, support and count-marker tests therefore apply in
their original order. No new pretyping assumption or carry argument
has been introduced.

The raw input [2x,0,0], ordinary numerical counter updates, exact
source-zero requirements, all-zero target, cyclic-entry graph and
first-positive-return acceptance are identical. In the positive
converse, first take the predecessor's complete construction and then
forget TV. There is no new width choice, no reconstruction of enormous
Pell coordinates, and no possible change in index parity.

For each recursively enumerable set of positive integers, use the same
fixed three-counter universal compiler and the same fixed constants
as the 114-operation predecessor. The resulting 113-operation system
has positive witnesses precisely for the inputs in that set. The
already counted input operation x+x is unchanged. No free variable
powers, uncounted loaders or omitted semantic checks are involved.

## 4. Exact arithmetic and evidence

The old support calculation and native TestV adapter use

    marker_forbidden=Zstar*H,
    program_V_rhs=V+marker_forbidden,
    program_native_TV=J+TV.

Retain the existing NV=J+V adapter and replace those three instructions
by

    marker_forbidden=Zstar*H,
    program_V_rhs=NV+marker_forbidden.

Compare NTV with program_V_rhs and delete the old raw-TV comparison and
the separate native-TestV adapter comparison in favor of that one
comparison. NV is supplied, so its use at this earlier point in the
instruction list does not introduce a forward register reference.

One addition, one positive unknown and one equation disappear:

    114-1=113=55M+58A,
    42-1=41 unknowns, 30-1=29 equations.

The checker expands all 29 source comparisons against the complete
113-instruction certificate. Twenty-eight retained source polynomials
are literally unchanged; the remaining one is the displayed residual
identity. The auxiliary norm correction remains at its original index.

Both full canonical examples are rerun through the predecessor, which
checks the stronger list of all 20 old outer residuals. The receipt
labels those inherited checks separately from the 19 new outer
equalities implied by the exact elimination identity. All twelve
native words, the packed integer, its exact central-binomial valuation
and the complete positive-kernel hypotheses remain unchanged. The
enormous Pell coordinates are established by the proved converse,
rather than numerically instantiated.
