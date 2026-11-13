# Independent prelaunch review: trace75 BFS model halt

**GO for one coordinated author check**, using the reviewed runner and outer
wrapper. This prelaunch review is not a Lean replay or a halt equivalence.

The checked client is `research/trace75-bfs-model-halt-prototype/`:

- source SHA-256 `bd7cde350d06e7c0f5e56c6df69bfdfe9d3622aaaaf45ce3b8a95d3a597f3069`;
- runner SHA-256 `56db6dbc8ab4eebb99e684eb197ef2b725bcfbcb3f2584881e59130aa378100c`;
- outer SHA-256 `84e1ae0d0bacdccccfcc7e5a2476becdeda94d49821433e5cf2df498b1c424ef`.

Under exact symbolic direct-BFS ports and a positive trace75 zero, the
proposed theorem takes the predecessor's original-table Word over the same
backward-mapped row, supplies its model definability, and composes marked-word
identification with machine soundness. Its conclusion is existence of a
model time t with `first (ArithmeticMachineRun215.run t)=0`. It is one model
direction; it is not a standard halt equivalence, iPRA endpoint or external
file binding.

`check.py` independently rehashes 48 pins, 20 regular client source/object
roots and matching PASS receipts, 1,977 project and 80 outside bundles,
including companion presence, bytes, targets and ordered first resolutions.
The captured `OldWordIdentification` and `ArithmeticWangSoundness` subtrees
have 526/42 and 135/8 project/outside modules. These checks reflect filesystem
state at audit time and inherit historical source/object, package and dynamic
limits.

In an isolated temporary copy, all 18 actual policy-function controls passed.
The outer wrapper rejected a modified runner before creating an attempt or
launching a child. Capture and audit the terminal after the coordinated run;
this review is not an author-check result.

`check.py` SHA-256 `eb433b4e51ac89bd57481ad6bf3a006c0b9761d4f3dda9970233b0dc2f70e01f`;
`result.txt` SHA-256 `4cecd4b664a2909d5e26983d6d01ff101ddc921e1efdbc0a0ac15b584b8a1e86`.
