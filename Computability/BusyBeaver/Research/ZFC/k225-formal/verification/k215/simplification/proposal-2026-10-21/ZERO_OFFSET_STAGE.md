# Second stage: eliminate the unused offset layer

This is a genuine simplification opportunity, but is lower priority than semantic
symmetry. All 2,240 certificate offsets are zero. Ordinary `RMBisim` already
provides `Bisim.symm`, `Bisim.halts_iff`, and `check_halts_iff`. Its certificate has
four fields `(a,b,j,k)`, compared with the five offset fields `(a,b,z,j,k)`.
The zero-offset layer contributes no mathematical content for this instance.

## Do not use the existing ordinary decoder unchanged

The actual definition is `decode n := decodeAux 128 n []`. The offset version is
`odecode n := decodeAux 512 n []`. Existing commentary describing 127/511-bit
limits is conservative/off by one relative to the fuel implementation: each
recursive call can consume one bit before fuel exhaustion.

The original K215 certificate has 622 pairs with a path longer than 128 bits;
all are on the second side, and the longest path is 176 bits. With 128 fuel,
these numbers decode only their low 128 bits, losing the remaining prefix.
Thus substituting current `RMBisim.entryOk` after deleting offset fields changes
622 pointer meanings and is not a valid certificate translation.

## Exact guarded translation

Parameterize the ordinary certificate checker by a pointer decoder
`d : Nat → List Bool` (equivalently by fuel, with d=decodeAux fuel · []). Its
soundness proof does not need injectivity, surjectivity or a numeric size bound
for d: the certificate denotes exactly the path pairs that d returns. The
existing `getc`, `entryOk`, `Rel`, and soundness proof use that same d uniformly.
Choose d=odecode, definitionally `decodeAux 512 · []`.

Define `erase` structurally on the offset certificate tree, preserving every
branch cut and replacing `(a,b,z,j,k)` by `(a,b,j,k)`. Require the explicit guard
`allO (fun x => x.offset == 0) T = true`. Then prove, in order:

1. `lookupC (erase T) j = (lookupO T j).map eraseEntry`. This holds for every T
   and j, even malformed trees, by structural induction preserving cuts.
2. The zero guard implies that every successful offset lookup returns z=0,
   using the existing `lookupO_all` lemma.
3. `countsOk 0 0 l1 l2 = true ↔ cntEq l1 l2 = true`. At offset zero, delta is
   identically zero; cast-injectivity turns integer count equality into natural
   count equality. The extra test at register5 is redundant: either5 occurs in
   l1++l2 and is already checked, or both counts are zero by `cnt_zero`.
4. For any A,B,j, `obranchOk t1 t2 T A B 0 j = true` iff the decoder-parameterized
   ordinary `branchOk_d t1 t2 (erase T) A B j = true`. Successful lookups use
   steps1–2, decoder identity is definitional, and counts use step3.
5. The zero guard plus `allO (oentryOk t1 t2 T) T = true` implies
   `allC (entryOk_d t1 t2 (erase T)) (erase T) = true`. At every test the offset
   guard is automatically true, and both successor branches use step4.
6. Apply ordinary `check_halts_iff_d` with the translated initial check and full
   entry check. The target theorem is exactly the existing `p215_halts_iff` for
   arbitrary register files. No logical weakening or new axiom is introduced.

Alternatively, generate the four-field data directly and recheck it with d512;
the old offset checker need not remain in the final dependency closure. For an
initial migration, retaining the old checker and proving the guarded translation
helps establish exact provenance but does not remove its checking cost.

## Expected value and limits

The improvement is mainly conceptual: the K215 source proof can use ordinary
bisimulation and ordinary natural-number counts, avoiding an apparently relevant
register-offset invariant that it does not need. It also removes one field per
entry and some small Boolean guards/casts. Unlike symmetry, no substantial
additional compiler-time saving has been measured or established. Most remaining
source-check work still traverses pointer paths and program segments.

A generic decoder parameter is preferable to globally changing `decode` from128
to512: older clients remain definitionally unchanged when instantiated with128,
while K215 explicitly chooses512. It is also preferable to duplicating all of
RMBisim as a separate 512-fuel checker. Keep the proven generic symmetry patch as
the first, lower-risk proposal; this second-stage checker refactor remains an
outlined theorem plan, not a compiled implementation.
