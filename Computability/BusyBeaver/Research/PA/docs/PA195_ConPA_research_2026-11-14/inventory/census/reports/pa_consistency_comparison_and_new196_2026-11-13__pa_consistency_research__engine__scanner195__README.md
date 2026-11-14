# Unproved195-state shortened-scanner candidate

This is **not an accepted consistency machine**. Its actual blank-run property
has not been proved or disproved here. It is retained as a concrete failed
implementation candidate, not as the requested successful sub196 construction.

Starting from the independently checked scanner_best196 table, redirect native
row23/0 from `0 L34` to `0 L75` and delete state34. The result has195 working
states,390 transitions, and one separate halt control. All195 working states are
syntactically reachable. `candidate.tm` uses initial control0 and halt195;
`candidate.native.tm` preserves the parent names (initial74, halt254).

The unrestricted arbitrary-frame checker fails96 of4,780 branch contracts.
After independently rebuilding the3673-site source CFG and auditing its trit
fixed point (4,270,098 pairs;4,792,890 edges), the strengthened affine checker
already fails site0, the zero branch of `CD5`, at source path000000. That
abstractly admitted failure rejects the simulation certificate and does not
alone supply a concrete blank-run counterexample.

There is also a concrete clean-frame contract failure: start the body at root84
on the standard candidate2 frame (site25, logical registers2,0,...,0,26 spare
blocks of value1, header distance48). Its first root return is after118 steps
at the correct head position0, but its tape differs in43 cells from the
required successor site27 frame (path1000100). The shortened machine has not
been shown to reach this standard frame from blank, so this observation is
carefully separated from its unknown blank-run consistency property.

Run `python3 check_scanner195.py` from the engine bundle directory to
reconstruct the exact candidate, regenerate its source-bound finite closure,
replay the concrete clean-frame mismatch, and reproduce the first strengthened
affine failure. The run stops after that failure; it does not claim to discharge
all remaining failed obligations.
