# Independent review of partial signed-transport recovery

PASS for the four stated partial conclusions: center-clause recovery, nontrivial whole-cell alignment of the positive rotation, occupancy of every cell, and horizontal overlap. No author correction is requested on the frozen version. This review does not promote those conclusions to the old vertical overlap or to a computation/soundness theorem.

Frozen author `/tmp/complete83_signed_transport_partial_recovery` pins:

- MD `5904b0d16501921473de2ef2bfc52dff612450808a4df8c8469f85f6cae848c7`.
- PY `63eb5647fe1208a78ce5592a48851d4c8d3a9fda2a4efc627d88ae7c1c93b247`.
- JSON `9370a15872113fee2859ab2d1d0e5dd1ad17edfb844cb29d118e00a0cc3499d6`.

The full author proof and helper were read. The precursor native-mask proof/source was independently reviewed in the immediately preceding packet; its code was not rerun. Relevant actual modified75/76/78 compiler definitions and geometric proof interfaces were read inertly. Exact author and dependency pins are checked by the new independent receipt. Earlier machine semantics and native Pell classification remain inherited, not freshly re-proved here.

## Proof challenge

**Cyclic subtraction.** Both `Pword` and `Nword` lie strictly between0 and `q−1`; their difference is nonzero because supplied `F` is in that interval. For a positive difference ordinary subtraction has initial/final borrow0. For a negative difference subtracting the extra unit starts and ends with borrow1 and returns the representative modulo `q−1`. Since raw digits lie in `[−4,V−2]`, only binary borrows occur. At `N_j=0`, any positive `P_j` kills the incoming borrow. This reasoning includes the cyclic boundary and does not assume cell-boundary borrows vanish in advance.

**Clean center.** The clean center is uniform across cells by the doubled-band separation. The case where a borrow enters a positive clause coefficient must be handled; rejecting a borrowed zero digit alone would not suffice. The note does handle it. If any native digit below `Emax` is nonzero, convolution by the positive highest-anchor coefficient gives an earlier positive digit at `T_j−Emax+f`, strictly after all negative support. It stops the borrow before the center. If there is no such digit, the cell is zero or highest-anchor-only, and its center value is divisible by the clause radix `A`. Since `A|V`, an incoming borrow makes the lowest `A`-digit `A−1`, violating mask `A−2`. Thus the center has no incoming borrow in every case. The exact old finite clause expression then types the cell, while ignored dummy digits remain unrestricted. No negative digit occurs thereafter in that cell, proving every cell-boundary borrow is0.

**Anchors.** At the origin Start supplies positive digits at `8M0` and `24M0`. The negative support misses their intervals through `9M0` and `27M0`, respectively, so both anchor tests are borrow-free. Their unshifted values are exactly1. Two odd rotated digits rule out intermediate bit residues and the single upper-dummy spill position. At residue0, the unique difference `18M0` in `E−E`, with the no-wrap bound on `L`, forces whole-cell alignment. The case of zero cell shift is excluded by the field mask's origin unit bit and the now-proved zero borrow into the origin, not by the altered vertical equations.

**Horizontal propagation.** An occupied right cell supplies a positive selector term at `H+s`, before every horizontal target, and after all negative support. An occupied center supplies a positive term at `33M0`, also after negative support and before `H`. These stop any incoming borrow in the two occupancy-mismatch cases. A lone one-hot tile contribution then violates a retained parity test. Thus adjacent occupancies agree; cyclic shift1 and the occupied origin force all cells occupied. The same center stopper makes every horizontal target exact, recovering the stated overlap. Ignored dummy contributions cannot enter tested targets by the actual compiler geometry.

The frozen text correctly says subtraction from `MF0 J` changes the lowest **three** bits. My draft challenge identified the earlier “two bits” wording; it was corrected before freeze. The new text preserves all old high tests and uses the correct origin low-bit test.

## Independent checks and limits

Only the newly written `/tmp/review_complete83_signed_transport_partial_recovery.py` ran. It gives:

- 39,918 exact cyclic-subtraction cases, including6,708 negative differences and20,322 positive stopping occurrences;
- 50 abstract layouts derived from the displayed geometry, checking5,400 pre-center stopping positions, anchor isolation/uniqueness and1,500 exact horizontal targets;
- 56 borrowed-occupancy obstructions and374 one-hot occupancy mismatch cases;
- the complete local vertical parity table, including the passing altered tuple `(incoming,P,N)=(1,0,1)`.

The abstract layouts are not claimed to be compiler outputs. These finite checks corroborate, rather than prove, the quantified argument. No inherited helper/source program was executed or imported, no actual native zero was generated, and no repository file was changed. Fresh normal generation and optimized-Python exact receipt comparison both passed from `/`.

The altered vertical relation is retained. In particular the locally passing digit `V−2` prevents simply deleting the negative term and invoking the old marker theorem. A separate vertical obstruction, if established, requires its own proof and review; it is not inferred in this partial packet. No arithmetic reduction, new witness bound or universal83 result follows here.

Independent frozen pins:

- PY `58215a6bfd27ed754877d12d0d0ca0428465b7186edcf4be97fb38a632b5199a`.
- JSON `c978cc8d48b1ac36dcf2d8771efa1113f526d889bc991b51d0a85227e6fef8ec`.
