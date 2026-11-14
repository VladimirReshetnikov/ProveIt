# First-three positive branch with blank tail: to dense 24

`PA194FirstThreeBlankTailTo24.markerFirstThreeBlankTailTo24` follows the
genuine first non-first marker entry when the first physical value is three,
the selected value is `k+1`, and the final file tail is zero. It crosses and
returns across the fixed finite file, follows the controller through dense 13,
14, 15, 16, and 17, and reaches dense 24. Both final packed halves are exact:
the left is `h = 2*zeros(2, zeros(6, u))+1`; the right is `1+4*w`, where the
Lean statement defines `w` from `k` and the returned file. The overall clock is
existential. The helper at dense 16 uses the model-uniform zero scan for `k`
and explicit table transitions; no standard-run transfer is used.

The block count is a fixed Lean natural number. The values in those blocks,
`k`, and the execution clock may be nonstandard model elements. The exact
marker input, nonempty following file, and zero final tail remain assumptions.
The result neither establishes that this input is reachable nor identifies
the dense-24 tape with a source frame. It does not prove an iPRA consistency
implication. The zero-selected branch is a separate theorem and does not
require the blank-tail assumption.

A fresh author two-module suffix replay passed against retained checked
prerequisite overlays, reporting `propext`, `Classical.choice`, and
`Quot.sound` and no `sorryAx`. The full nested checker
`check-first-three-blank-tail-to24.sh` is supplied but has not been run.
