# Full PA194 AX source execution

`PA194AXReadable.complete` gives the result as an explicit macro-store
configuration, and `PA194AXComplete.complete` proves that the actual pinned PA194 source,
starting at site 50, reaches site 3660 for every choice of natural register
inputs and arbitrary untouched-register frame. Its top is the old guarded
formula: zero if either label comparison matches, and `oldBundle` otherwise.
The resulting stack has the separate diagonal formula followed by the eight
PA196 heads and the saved incoming top. The guard also clears the five
working registers and preserves the stack and other framed registers.

This composes the 251 checked source macro contracts from `../pa194-ax-core`
with source-specific guard row equalities and the generic comparison proof.
The gate modules adapt the upstream PA196 `AXGateBinding`, `AXGateSteps`, and
`AXGate` proofs to PA194 source indices; all concrete row equalities are
rechecked by Lean. Both theorems print `[propext, Quot.sound]` and is about
standard finite source executions. It is not yet an internal PRA/iPRA proof
or a PA-refutation translation, and it does not by itself establish Con(PA).
The source tree comes from the pinned Python archive-grammar translation
described in `../pa194-source-tree/README.md`.

From the repository root run:

```sh
Computability/BusyBeaver/Research/PA/pa194-ax-guard/check.sh
```

This rebuilds the pinned source and all 251 core contracts in an isolated
temporary directory, then checks the guard and full composed execution.

The full guard check passed from a fresh build. The readable corollary was
subsequently checked against the retained fresh-build objects; the script
now also checks that corollary.
