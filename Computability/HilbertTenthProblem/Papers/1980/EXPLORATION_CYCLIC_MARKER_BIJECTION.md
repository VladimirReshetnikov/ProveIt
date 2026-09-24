# Unique End already implies unique Start in the helical tableau

For every genuine cyclic word of the fixed window relation used by the
[81-operation theorem](FIXED_RAW_UNIVERSAL_81_PROOF.md), its occurrences of
the fixed Start and End windows are in a canonical bijection. In particular,
**exactly one End implies exactly one Start**. If a separate arithmetic
argument supplies Start at index0, this is the unique Start required by the
existing raw-input semantic theorem.

This lemma concerns the genuine local relation, after the field masks and
period alignment have been decoded. It does not replace that decoding or
assert an operation count. The [checker](../verification/explore_cyclic_marker_bijection.py)
and [receipt](../verification/explore_cyclic_marker_bijection.json) distinguish
finite phase tests from genuine helical tableau tests.

## 1. Work on cyclic indices, not on copies in the covering plane

Let N>=1 and let h be any stride. Suppose a cyclic word of allowed
three-by-three windows satisfies both exact overlap relations at offsets
0,-1,-h. Their center projection gives a valid helical configuration under
the index map

    (physical_column,time) -> i-physical_column-h*time mod N.

Equivalently we may work directly with the N projected center tiles.
Physical right is the cyclic permutation i->i-1; physical left is i->i+1.
In particular, a maximal horizontal run and its two endpoints are defined
on this finite cyclic set. No claim that h divides N is used.

Recall the initialization phase graph

    L -> L or I,    I -> I or Q,    Q -> R,    R -> R.

A vertical boundary requires phase L at the first interior position and
phase R at the last. Adjacent nonboundary columns on one initialization
row have the same horizontal-boundary track above them. The exact local
rules assign initialization phases precisely on such rows.

Consequently any I-phase run containing a Start or End is proper and
finite. Its immediate left neighbor is phase L and its immediate right
neighbor is phase Q. It cannot end against a vertical boundary, since an
I-phase tile may not be the first or last interior tile. The left and
right scans terminate before N steps: a Start already has Q to its right,
and an End has L to its left, so in either case the cycle is not all I.

## 2. The endpoints are exactly the two fixed windows

The normalized first transition writes the origin flag2 and stays at Q,
entering a distinct nonhalting state q1. Consider a proper I-run of length
u>=2. Its whole segment belongs to one initialization row, with headless
ones at its I positions, blanks at the adjacent L positions, and the
unique initial q0 head at the adjacent Q.

The next row inside this strip cannot be a horizontal boundary: q0 is
nonhalting, and the boundary track is uniform between the vertical
boundaries. The exact first-step rule therefore leaves all I positions
headless1, leaves the adjacent L blank and headless, and changes Q to
symbol2 with head q1. All these next-row interior phases are absent.
Their preceding boundary-row tiles are H.

Thus the last I of the run has exactly the fixed Start window

    H H H
    I I Q(q0,1)
    1 1 Q(q1,2),

with the phase and head annotations as in the 81 proof. The first I has
exactly its fixed End window

    H H H
    L I I
    0 1 1.

Conversely the fixed Start contains the phase substring I,I,Q, so it is
the last I of such a run; fixed End contains L,I,I, so it is the first I.
There is exactly one of each for every run of length at least2. A run of
length1 has neither. An all-I cyclic row has neither and makes no
contribution to the bijection.

## 3. The maps are inverse even with aliased covering positions

Given a Start occurrence s in Z/N, scan left through I phases to the
first I in its maximal run. Call that index e(s). Section2 proves that
e(s) is an End. Given an End e, scan right through its I-run to its last
I; call that index s(e). Maximality and the two boundary phases imply

    s(e(s))=s,  e(s(e))=e.

These identities are on cyclic residues themselves. If two Starts had
the same End residue, scanning right from that residue would recover
both, so their residues would be equal. Different physical copies in
the periodic covering plane cannot create an exception.

The displacement from a Start to its associated End, walking left, is
u-1, strictly between0 and N. If End is unique and is prescribed at
index x with 0<x<N, while Start is supplied at0, their bijection implies
that this is the same I-run and that x=u-1. Its initial unary length is
u+1=x+2. The existing finite-rectangle and halting argument in the 81
proof then identifies acceptance of precisely the raw input x.

This direct argument also covers intervening unmarked one-I strips and
noncanonical strides. It does not infer uniqueness of unrelated boundary
rows or vertical strips, which is unnecessary.

## 4. Verification boundary

The checker exhausts closed phase words of lengths1 through18 in the
initialization-strip graph, including vertical separators. It checks the
two inverse maps, runs crossing numeric index0, multiple marker pairs,
and short unmarked runs. This graph enumeration is a focused phase test;
it is not represented as an enumeration of all tableau tiles.

Separately, the checker constructs actual accepting helical words from
the retained machine implementation, verifies every genuine local window
and both overlaps, and checks the inverse maps against the exact marked
windows. Rotations and doubled words test different cyclic origins and
multiple occurrences. It includes one-I inputs with neither marker and
valid presentations where h does not divide N. These finite cases support
the general cyclic-index proof above; they do not replace it.
