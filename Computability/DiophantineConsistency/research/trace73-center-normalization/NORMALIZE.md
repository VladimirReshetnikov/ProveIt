# Normalize a positive trace75 zero to a trace73 zero

`Trace75NormalizeCenter.positive_zero_to_center` is checked in every supported
IΣ₁ model. For arbitrary natural ports satisfying model beta ≥ 31, low < beta
and high < 2 beta, and an actual positive trace75 zero, it constructs a
positive zero of the literal trace73 evaluator at the **same ports**. K0 is
arbitrary. There is no assumed center bound or sign for the carrier.

The proof uses one tuple `tau,f,V0,Z0,y` from the actual trace75 adjacent
equations. Existing model theorems supply nonnegative transport `B=b*t`, the
exact offset `e=(XY)*rho`, and `K=H*kappa`. The new [root bound](KAPPAROOT.md)
gives `kappa<f≤tau*f*y`. From the actual carrier-square equation, either
`Z=M*(tau*f*y)` or `Z=-M*(tau*f*y)`. In the first case the carrier balance
directly yields `V²B<n`. In the second case the [all-ring sign flip](SIGNFLIP.md)
increases n by `2*tau*f*y`, keeps the trace75 graph value zero, and gives the
same strict center bound. Trace75's checked nonnegative transport supplies
`V²B≥0`; the existing model substitution then yields a positive trace73 zero.
The sign flip changes only n, so it does not identify any independently chosen
root or quotient witnesses.

This is a **one-way positive-zero implication**. It does not prove that an
arbitrary positive trace73 zero has `V²B≥0`, does not prove a trace73/75
equivalence, a machine halt theorem or an iPRA endpoint, and does not prove
JSON/PDF semantics. Symbolic fixed ports must still be specialized separately.

The bounded author run `observations/normalize-attempt02/` and tool session
4767 exited 0 with no diagnostics. The theorem's axiom report is
`[propext, Classical.choice, Quot.sound]`; the object
`/tmp/trace75-normalize-qdmz3b0v/Trace75NormalizeCenter.olean` has SHA-256
`c9db6c31f50c7b19480d7f8f0653e053a77313b7765363ffdd5967b2f1195148`.
The source, runner and terminal hashes are
`f1737d306452a44076e18001a513ca237ab1baaff95f30852ea28c0a9623e797`,
`a232c90cad80313593f3af08a1b4feadf9c9e81af69e165c2c66a73aa86559e1`, and
`5b2e91e5c5f7947d42365237740e719b9cbd18de2d3aaa55fcebec4da0e1702c`.
Attempt01 failed on cast/definitional-equality details and is retained.

The direct fresh trace75 transport, quotient and offset providers, the new
root/sign-flip clients and the earlier trace73 model-sign client are pinned.
The checked trace75 graph and difference-ring objects match the fresh provider;
the complete combined 73/75 serialized closure, historical producer inputs,
supplemental, package-transitive and dynamic ancestry remain inherited. The
author observed the tool exit but did not retain a separate outer receipt. No
independent Lean replay, source/receipt audit, or file-binding theorem is
claimed by this packet.
