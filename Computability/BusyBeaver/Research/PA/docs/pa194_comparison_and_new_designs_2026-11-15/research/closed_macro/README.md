# Closed source-routine reassociation

This is an additional bounded search, not a new certified machine.
It rearranges closed subroutines outside the AX reader while retaining
their named native control entries. Anonymous binary readers are shared
by literal row signature, unused controls are removed, and the resulting
raw tables are priced with the included one-bit-history matching screen.

Twenty-five individual source rewrites were checked against the complete
3,673-instruction resolved graph. Twelve had an optimistic price of194,
eleven195 and two196. The twelve194 candidates passed their local fold
certificates and were independently subjected to further physical merge
searches, retained under `../physical/inputs/closed/`. Complete physical
source correctness was not established for them; they are search inputs.

Joint searches over two, three and four selected rotations generated
13,125 distinct raw tables. No projected count below194 was found.
The complete recorded histogram is:

| Projected states | Raw tables |
| --- | ---: |
|194|847|
|195|2535|
|196|3759|
|197|3525|
|198|1958|
|199|501|

The single rewrite graph checks and closure criterion motivate the joint
search. All joint tables were syntactically priced; they were not all
given complete source-frame certificates. The price is specific to this
lowerer and the supplied raw-action matching screen, not a general lower
bound. The screen can suggest incompatible folds; any positive result
would need its complete simultaneous-fold and physical proofs.

`recorded/singles.json` freezes the exact25 selected rewrites.
`recorded/joint_results.json` freezes the full13125-table result.

```sh
python3 -B search.py
python3 -B search.py --full
```

The default repeats the292 distinct two-rotation inputs; `--full` includes
the2119 additional three-rotation and10714 additional four-rotation inputs.
The output is `replay.json`; recorded files remain unchanged. The full run
took approximately159seconds in the original environment, with no193hit.
Fresh portable replay of the two-rotation stage reproduced its exact
histogram. Python3.10+ and the standard library suffice.

The pinned primary inputs and the build/source-resolver and matching
utilities are attributed imports from the incoming loop-continuation
packet. Its source notices are in `licenses/`. The closed-routine lowering,
rotation selection and joint search are new research in this delivery.
