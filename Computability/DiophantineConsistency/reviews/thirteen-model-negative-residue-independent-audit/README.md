# Independent audit of the model negative-ordinate residue

The read-only audit of commit `9d08926d17` exited 0. It verifies the author
packet's recorded outer wrapper exit 0 in session 66854, both five-module
suffix chains, all ten recorded compiler and dependency-check exits, the
exact source/object hashes, ordered direct imports, and all 64 parent project
links per side. Corresponding objects match. The newly merged
`ArithmeticOddOrdinateResidue` is rebuilt as a suffix; it is not part of
the earlier pinned 70-source parent.

The theorem assumes an `IΣ₁` arithmetic model, natural `I,R,b`, `I>=2`,
`b | I`, and `R % 4 = 3`. It gives a model-natural `h` satisfying
`ycoord R (I-2)+1 = 4*b*h`. The proof uses the odd-ordinate residue modulo
`4*I²` and the supplied divisibility. Although the theorem has no separate
`b>0` hypothesis, `b=0` is incompatible with `b | I` and `I>=2`. A finite
check of 102 standard cases supplements the proof; it is not an
arbitrary-model proof.

Each sibling's older dependencies report six warnings, all deprecations of
`push_neg`; the final residue source reports no warnings and its one axiom
report lists `[propext, Classical.choice, Quot.sound]` without `sorryAx`.
These are Lean metatheory dependencies, not object-level iPRA axioms. The
author documents an earlier failed elaboration that printed `sorryAx`; it is
not the paired result. This audit checks the recorded outputs and does not
independently rerun Lean.

The result is a positive ordinate residue. It does not itself construct the
intended negative signed ordinate or positive carrier coordinate, prove the
69-operation converse, calibrate a fixed-port checker, or establish an iPRA
theorem. The two suffix chains share the historical Foundation/package
provider and compiler; package-transitive and dynamic ancestry and the
unobserved original Foundation wrapper exit remain outside this evidence.

`CHECK.json` records the exact source/object hashes, parent links and finite
cases. `terminal-observation.json` binds the actual audit exit to its receipt.
Run while the historical temporary outputs remain available:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/thirteen-model-negative-residue-independent-audit/audit.py
```
