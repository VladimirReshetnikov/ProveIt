# Independent source review: actual-graph q-balance

Reviewed the pinned, unelaborated sources in
`research/ordinary13-residue-qbalance-graph-draft/` and their specified
upstream interfaces. The author's checker reproduces. This review adds an
independent exact sparse-polynomial calculation: run
`python3 -I -S -B check.py` in this directory or by absolute path. The checker
pins the source bytes and verifies the two displayed polynomial identities
for indeterminate variables. It does not check Lean elaboration or any model
hypothesis.

Write `s=v 7+1`, `Y=q³s`, `U=Yq²`, `a=XY+Y`, `H=3+4a`, and
`W=4Xqsw`. The exact-index source gives
`k=R+1+4XY²w`, using its same returned `w`. Substitution gives the exact
free-ring identity `4XY²w=UW`. Under that substitution, the original
oriented-root equation has defect equal to `qY` times the advertised
q-balance defect. Thus the source's cancellation is justified in its
intended nonnegative model when `q>0` and `Y>0`; these hypotheses are explicit
in `q_balance`, and the graph caller proposes to derive them from `q≥2` and
`Y≥q³`. No q-divisibility, coprimality, or sign of an integer difference is
needed for this step.

The actual-graph client calls `actual_main_balance` with the stated U, Y, k,
and gap bounds, and calls `exact_indices_of_graph` with graph zero, positive
J, beta and X, the gap, and the rank window. Its 13-pattern destructuring
matches the five existential outputs and their eight conjuncts: the extracted
`n`, `w`, lower bound, `2n=R+1`, and k decomposition have the advertised
positions. The fixed model tuple is still arbitrary `p`; the compact fixed
ports and their model representation are not established by this client.

The next client explicitly requires `q≥46`, `q∣3X`, the first Pell ordinate
at that same `n`, and both main recurrence coordinates at the **same**
`main` appearing in the q-balance. This is a necessary interface distinction:
`exact_indices_of_graph` does not export its prior first-ordinate equation,
and the positive oriented `main` is not identified here with its Pell
x-coordinate. Even if each witness exists separately, identifying the
corresponding coordinates remains a separate source/provider obligation. The
coordinate client may take the balance and coordinates as assumptions, but
its conclusion is not unconditional evidence of their graph extraction.

The q-balance client, its imported graph/index providers, and the downstream
power client are source proposals; their tactic calls, casts, import closure,
compiled providers and axiom reports have not been checked here. This review
makes no eta-zero extension, fixed-byte/PDF binding, end-to-end equivalence,
or internal-iPRA proof claim.
