# Conditional positive transport from the parent carrier equation

[`Model69Transport.lean`](Model69Transport.lean) proves the following in an
arbitrary `IΣ₁` model. Given model-natural `b,q,K,w,F,alpha,C,z` satisfying

```
q=b+1,  z>0,  C>0,  F+alpha+C=q,  F<q,  q≤w,
(K+w)*q+q = (K+w)*(F+alpha)+F+z*(q-1)+1,
```

let `G=b*(z-1)`. Then `G>0`, `b∣G`, and
`(K+w)*C=F+G`. Thus `G` supplies precisely the positive, divisible transport
hypotheses of the [conditional fresh-private seed](../thirteen-model-fresh-private/README.md),
provided its other assumptions are established.

This is a **conditional scalar model lemma**. It does not prove that its
hypotheses follow from a particular positive Carrier65 zero, does not bind
`C` and `G` to the 69-row literal, and does not prove `R%4=3`, a model
converse, a fixed-port checker calibration or an internal iPRA derivation.
In the proposed 2011-port application, `b=beta*J` and `C=q-F-alpha`; their
zero-to-hypotheses derivation, including `q≤w`, still needs its own proof.
The phase-split2471 and 2011 tuples are distinct.

## Paired replay and prior failures

[`replay.py`](replay.py) compiles the source separately on both sides of the
[independently audited 70-source parent](../../reviews/ordinary12-coexistence-pair-independent-audit/README.md),
with `-M4000 -j1`, direct-import and fixed-source checks, and parent comparator
checks before and after. Session 61493 actually exited 0 and printed
`PASS_PAIRED_THIRTEEN_PARENT_TRANSPORT 60b37d4d3fca76ff0be2db498c5959ff2fc987517d5fdae4ff0c961da4c145ee`.
The [receipt](replay-receipt.json) records both child compiler/dependency
exits and matching object hashes; the [terminal observation](terminal-observation.json)
records the wrapper exit. Both copies report `[propext, Classical.choice,
Quot.sound]`, no warnings and no `sorryAx`. This suffix has not yet received a
separate independent audit. Package-transitive/dynamic ancestry and the
original Foundation wrapper's unobserved exit remain inherited.

The first exploratory command exited 1 because the input lay outside Lean's
implicit root directory. Session 92858 then exited 1 with an unfinished ring
goal and printed `sorryAx` after a tactic was scoped incorrectly. Session
86357 exited 0 but warned that an extra `b>0` premise was unused; it was
removed. Session 13241 actually exited 0 without warnings for the final
stronger theorem, which is the source later paired above. None of the failed
attempts is treated as proof evidence.
