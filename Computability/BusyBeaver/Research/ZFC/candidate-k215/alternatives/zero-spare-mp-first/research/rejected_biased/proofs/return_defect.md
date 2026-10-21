# A physically proved machine with the wrong control return

The archived scratch-biased 215-state table is not a new consistency machine. Its complete physical certificate proves the stated primitive program, but that program does not have the scheduler asserted in its research README.

The original context-root return was CC3 at source address 10011. It returned to ordinal 0. Replacing that leaf by (CI6,CC3) moves the return to 100111. A structured continue counts right ancestors. The third right ancestor now starts at prefix 1, whose first leaf is ordinal 23, the command selector. It does not start at the scheduler, ordinal 0. The added right ancestor was not compensated by changing CC3 to CC4.

The two independent CFG resolvers in verify.py agree on every one of the 4,733 source occurrences. In particular, the literal return is

- ordinal 4696: CI6;
- ordinal 4697, address 100111: CC3, target 23;
- ordinal 23: CD3, whose zero branch targets 4698, the short-transfer clear-top loop.

At every normal AX or MP return, the inherited local contracts give selector A=0, cache H=0 and arithmetic scratches X=Y=0. Let the retained top T=t and the other registers be arbitrary naturals. The literal suffix behaves as follows.

1. CI6 sets X=1. CC3 returns to the selector. Its A=0 branch enters short transfer.
2. The clear-top loop consumes t and leaves T=0.
3. The copy-cache loop starts with H=0, so its first phase does nothing. Its restoration phase consumes the already present X=1 and increments H once. Thus H=1 and X=0.
4. The inherited NIP test increments X to 1 and compares H with that single unit. The equality branch reaches CH at ordinal 4718. The encoded stack is not inspected.

This is a universal natural-number calculation, not a finite-test extrapolation. The number of nonhalt source primitives executed from ordinal 4696 to the CH entry is 2t+15. The retained sample t=42 reaches CH after 99 such steps, followed by the halt primitive itself. Its complete local trace is in evidence/local_halt.json; verify.py reproduces it independently and checks t=0 through 100 as additional corroboration.

The inherited exact blank bootstrap enters the interior of an AX invocation. That AX arithmetic terminates on its finite natural parameters and normally returns with the stated zero registers. Consequently its remaining suffix inevitably reaches this false halt. This conclusion uses the archived AX macro contract and physical simulation; this packet does not claim a measured literal whole-blank halting step count.

The defect is logical control flow, not a defect in the all-natural physical checker. Its 6,152 cases can all be correct while implementing the wrong register program. The copied runtime receipt is provenance, not a newly rerun physical certificate.
